"""Run: python3 -m unittest discover -s tools/mir -p test_mir_stats.py -v.

Set RAPX_TEST_CARGO_RAPX to a built cargo-rapx to also run it on the mir_demo fixture.
"""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("mir_stats", ROOT / "tools/mir/mir_stats.py")
ms = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ms)

LOG = (ROOT / "tools/mir/testdata/mir_demo.log").read_text()
FIXTURE = ROOT / "rapx/tests/analyze/mir_demo"


def by_path(metrics):
    return {m["path"]: m for m in metrics}


def run_main(*argv):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        ms.main(list(argv))
    return out.getvalue()


class ParseTest(unittest.TestCase):
    def setUp(self):
        self.bodies = ms.parse(LOG)
        self.metrics = by_path(ms.measure(b) for b in self.bodies)

    def test_every_body_kind(self):
        kinds = {b["path"]: b["kind"] for b in self.bodies}
        self.assertEqual(len(kinds), 19)
        self.assertEqual(kinds["LIMIT"], "constant")
        self.assertEqual(kinds["GREETING"], "static")
        self.assertEqual(kinds["Buf::push"], "method")
        self.assertEqual(kinds["closure_user::{closure#0}"], "closure")
        self.assertEqual(kinds["add_one::{closure#0}"], "async_fn")
        self.assertEqual(kinds["zeros::{constant#0}"], "constant_expression")
        self.assertEqual(kinds["Shape::Circle"], "tuple_variant")
        self.assertEqual({b["crate"] for b in self.bodies}, {"mir_demo"})

    def test_locals_and_blocks(self):
        push = next(b for b in self.bodies if b["path"] == "Buf::push")
        self.assertEqual(push["locals"][1], dict(index=1, ty="&mut Buf", names=["self"]))
        self.assertEqual(push["locals"][2]["names"], ["b"])
        self.assertEqual([b["index"] for b in push["blocks"]], list(range(6)))
        self.assertEqual(push["blocks"][-1]["lines"], [("return", "Return")])

    def test_branching_and_calls(self):
        push = self.metrics["Buf::push"]
        self.assertEqual((push["blocks"], push["cyclomatic"], push["named_locals"]), (6, 2, 2))
        self.assertEqual([c["callee"] for c in push["callees"]],
                         ["std::vec::Vec::<T, A>::len", "std::vec::Vec::<T, A>::push"])
        self.assertTrue(all(c["krate"] != 0 for c in push["callees"]))
        self.assertEqual(self.metrics["sum"]["cyclomatic"], 2)
        self.assertEqual(self.metrics["area"]["cyclomatic"], 2)
        self.assertEqual(self.metrics["call_ptr"]["indirect_calls"], 1)
        self.assertEqual(self.metrics["closure_user"]["callees"][0]["krate"], 0)

    def test_cleanup_and_drop(self):
        d = self.metrics["dropper"]
        self.assertEqual((d["blocks"], d["cleanup_blocks"], d["drops"]), (6, 3, 1))
        # Unwind edges into cleanup blocks do not add branches.
        self.assertEqual(d["cyclomatic"], 1)

    def test_unsafe_signals(self):
        f = self.metrics["Buf::first_unchecked"]
        # `p` plus the `*const ()` temporary of the compiler's null check; only `p` is dereferenced.
        self.assertEqual((f["raw_ptr_locals"], f["raw_ptr_derefs"]), (2, 1))
        self.assertEqual(f["raw_ptr_deref_sites"], ["bb2: _0 = copy (*_2)"])
        self.assertEqual(f["runtime_checks"], {"null_deref": 1})
        self.assertEqual(f["casts"], {"PtrToPtr": 1, "Transmute(compiler)": 1})
        a = self.metrics["add_one::{closure#0}"]
        self.assertEqual(a["runtime_checks"], {"coroutine_resume": 2, "overflow": 1})
        self.assertEqual(a["casts"], {"Transmute(compiler)": 1})

    def test_tolerates_colors_and_missing_prefix(self):
        colored = "\n".join(f"\x1b[32m{line}\x1b[0m" for line in LOG.splitlines())
        bare = "\n".join(ms.LOG_PREFIX.sub("", line) for line in LOG.splitlines())
        for text in (colored, bare):
            self.assertEqual([b["path"] for b in ms.parse(text)], [b["path"] for b in self.bodies])

    def test_old_format_is_rejected(self):
        old = "10:00:00|RAPx|INFO|: Show MIR\n10:00:00|RAPx|INFO|: DefId(0:5 ~ demo[e4ae]::LIMIT)\n"
        with self.assertRaises(ms.FormatError):
            ms.parse(old)


    def test_interleaved_output_is_rejected(self):
        lines = LOG.splitlines()
        start = next(i for i, l in enumerate(lines) if "MIR [method] Buf::push" in l)
        # Swap two local declarations, as parallel rustc processes would.
        lines[start + 2], lines[start + 3] = lines[start + 3], lines[start + 2]
        with self.assertRaisesRegex(ms.FormatError, "CARGO_BUILD_JOBS=1"):
            ms.parse("\n".join(lines))


class CastTest(unittest.TestCase):
    def classify(self, text, types=None):
        return ms.classify_cast(text, types or {})

    def test_user_and_compiler_transmutes(self):
        self.assertEqual(self.classify("_0 = move _2 as u32 (Transmute)", {2: "f32"}), (0, "Transmute", False))
        self.assertEqual(self.classify("_5 = copy _4 as usize (Transmute)", {4: "*const ()"}),
                         (5, "Transmute(compiler)", False))
        box = ("_52 = copy (((_1.3: std::boxed::Box<hir::Hir>).0: std::boxed::BoxRaw<hir::Hir>).0: "
               "core::ptr::NonNull<hir::Hir>) as *const hir::Hir (Transmute)")
        self.assertEqual(self.classify(box), (52, "Transmute(compiler)", True))
        self.assertEqual(self.classify("_40 = copy (_34.0: std::boxed::BoxRaw<T>) as *const T (BoxDerefTransmute)"),
                         (40, "BoxDerefTransmute", True))

    def test_cast_forms(self):
        self.assertEqual(self.classify("_4 = move _5 as &[u8] (PointerCoercion(Unsize, Implicit))"),
                         (4, "PointerCoercion(Unsize)", False))
        self.assertEqual(self.classify("((*_1).0: u32) = move _11 as u32 (IntToInt)"), (None, "IntToInt", False))
        self.assertEqual(self.classify("_3 = copy ((_9 as Some).0: u8) as u32 (IntToInt)"), (3, "IntToInt", False))


class CliTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.log = self.tmp / "mir.log"
        self.log.write_text(LOG)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def test_markdown_report(self):
        out = run_main(str(self.log), "--top", "3")
        self.assertIn("## MIR statistics: mir_demo", out)
        self.assertIn("- bodies: 19 (fn 13, const 4, ctor 2)", out)
        self.assertIn("| add_one::{closure#0} | async_fn | 3 |", out)
        self.assertIn("| Buf::first_unchecked | 1 | `bb2: _0 = copy (*_2)` |", out)
        self.assertIn("- toolchain: unknown (statistics from a saved log)", out)
        self.assertIn("- callee crates: std 12 (92%), mir_demo 1 (7%)", out)

    def test_json_report(self):
        data = json.loads(run_main(str(self.log), "--format", "json"))
        crate = data["crates"]["mir_demo"]
        self.assertEqual(crate["by_category"], {"fn": 13, "const": 4, "ctor": 2})
        self.assertEqual(crate["fn_totals"]["indirect_calls"], 1)
        self.assertEqual(crate["transmute_bodies"], [])
        self.assertEqual(len(data["bodies"]), 19)

    def test_show_prints_one_body(self):
        out = run_main(str(self.log), "--show", "dropper")
        self.assertTrue(out.startswith("MIR [function] dropper (DefId("))
        self.assertIn("drop(_1) -> [return: bb3, unwind terminate(cleanup)] @ Drop", out)
        self.assertNotIn("MIR [function] sum", out)
        with self.assertRaises(SystemExit):
            run_main(str(self.log), "--show", "no_such_fn")

    def test_rejects_unrelated_input(self):
        (self.tmp / "other.log").write_text("Compiling foo\n")
        with self.assertRaises(SystemExit):
            run_main(str(self.tmp / "other.log"))


@unittest.skipUnless(os.environ.get("RAPX_TEST_CARGO_RAPX"), "RAPX_TEST_CARGO_RAPX is not set")
class RealCompilerTest(unittest.TestCase):
    def test_run_on_fixture(self):
        bin_dir = str(Path(os.environ["RAPX_TEST_CARGO_RAPX"]).parent)
        crate = Path(tempfile.mkdtemp()) / "mir_demo"
        shutil.copytree(FIXTURE, crate, ignore=shutil.ignore_patterns("target", "MIR_dot_graph"))
        old_path = os.environ["PATH"]
        os.environ["PATH"] = bin_dir + os.pathsep + old_path
        try:
            # No --toolchain: the toolchain of this RAPx checkout is picked up.
            data = json.loads(run_main("--run", str(crate), "--format", "json"))
        finally:
            os.environ["PATH"] = old_path
            shutil.rmtree(crate.parent)
        self.assertEqual(data["crates"]["mir_demo"]["by_category"], {"fn": 13, "const": 4, "ctor": 2})
        self.assertEqual(data["toolchain"], ms.repo_toolchain())


if __name__ == "__main__":
    unittest.main()
