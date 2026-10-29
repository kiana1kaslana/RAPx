#!/usr/bin/env python3
"""Turn `cargo rapx analyze mir` output into per-body and per-crate statistics.

Usage:
  python3 tools/mir/mir_stats.py --run CRATE_DIR [--toolchain NIGHTLY] [--save-log FILE]
  (without --toolchain, the toolchain active in this RAPx checkout is used)
  python3 tools/mir/mir_stats.py mir.log            # or `-` for stdin
Options: --format md|json, --top N, --show SUBSTRING (print the MIR of matching bodies).
"""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
ANSI = re.compile(r"\x1b\[[0-9;]*m")
LOG_PREFIX = re.compile(r"^\d\d:\d\d:\d\d\|RAPx\|[A-Z]+\|: ")
HEADER = re.compile(r"^MIR \[(?P<kind>[^\]]+)\] (?P<path>.*) \((?P<def_id>DefId\(\d+:\d+ ~ (?P<crate>[^\[]+)\[.*\))\)$")
LOCAL = re.compile(r"^_(?P<idx>\d+): (?P<ty>.*?)(?: @ (?P<names>.+))?$")
BLOCK = re.compile(r"^bb (\d+) \{$")
LINE = re.compile(r"^    (?P<text>.*) @ (?P<kind>[^@]+)$")
CALL = re.compile(r"^Call: (?P<callee>.*) #(?P<krate>\d+):(?P<index>\d+)$")
SUCC = re.compile(r"(?:(?P<label>[\w-]+): )?bb(?P<bb>\d+)")
DEREF = re.compile(r"\(\*_(\d+)\)")
CAST = re.compile(r"^(?P<dst>.+?) = (?:copy |move )?(?P<src>.*) as (?P<target>.*) "
                  r"\((?P<cast>\w+)(?:\((?P<detail>\w+)[^()]*\))?\)$")

CONST_KINDS = {"constant", "static", "constant_expression", "associated_constant", "inline_constant"}
CHECKS = [
    ("overflow", ("attempt to compute", "attempt to negate", "attempt to shift")),
    ("bounds", ("index out of bounds",)),
    ("div_by_zero", ("attempt to divide", "attempt to calculate the remainder")),
    ("null_deref", ("null pointer dereference", "null reference produced")),
    ("misaligned", ("misaligned pointer dereference",)),
    ("coroutine_resume", ("resumed after",)),
]


def classify_cast(text, types):
    """Return (destination local, cast label, is_box_deref) for a cast statement.

    rustc emits some transmutes itself; they are labelled `Transmute(compiler)`:
    `*boxed` is lowered to a transmute of the Box internals into a raw pointer
    (`BoxDerefTransmute`, or `Transmute` from a `BoxRaw`/`NonNull` field), null and
    alignment checks transmute `*const ()` to `usize`, and async bodies transmute
    their resume argument. The match is heuristic, on the types involved.
    """
    m = CAST.match(text)
    if not m:
        return None, "Other", False
    dst = int(m.group("dst")[1:]) if re.fullmatch(r"_\d+", m.group("dst")) else None
    src, target, cast = m.group("src"), m.group("target"), m.group("cast")
    box_deref = cast == "BoxDerefTransmute" or (cast == "Transmute" and "std::boxed::BoxRaw<" in src)
    if cast == "Transmute" and (
            box_deref
            or (types.get(int(src[1:])) if re.fullmatch(r"_\d+", src) else None, target) == ("*const ()", "usize")
            or target.startswith("std::ptr::NonNull<std::task::Context")):
        cast = "Transmute(compiler)"
    elif m.group("detail"):
        cast = f"{cast}({m.group('detail')})"
    return dst, cast, box_deref


class FormatError(Exception):
    pass


def category(kind):
    if kind in CONST_KINDS or "static" in kind:
        return "const"
    if kind.endswith(("_variant", "_struct")):
        return "ctor"
    return "fn"


def clean_lines(text):
    for raw in text.splitlines():
        yield LOG_PREFIX.sub("", ANSI.sub("", raw)).rstrip()


def parse(text):
    """Split the log into bodies: header, locals, basic blocks and the raw MIR text."""
    bodies, body, block = [], None, None
    saw_mir = False
    for line in clean_lines(text):
        if line == "Show MIR":
            saw_mir = True
            continue
        m = HEADER.match(line)
        if m:
            body = dict(m.groupdict(), locals=[], blocks=[], text=[line])
            bodies.append(body)
            block = None
            continue
        if body is None:
            continue
        if not line:
            continue
        m = BLOCK.match(line)
        if m:
            body["text"].append(line)
            block = dict(index=int(m.group(1)), cleanup=False, lines=[])
            body["blocks"].append(block)
            continue
        if block is None:
            # Outside a block only local declarations belong to the body; cargo and
            # other RAPx log lines are skipped.
            m = LOCAL.match(line)
            if m:
                body["text"].append(line)
                names = m.group("names")
                body["locals"].append(dict(index=int(m.group("idx")), ty=m.group("ty"),
                                           names=names.split(", ") if names else []))
            continue
        body["text"].append(line)
        if line.startswith("CleanUp: "):
            block["cleanup"] = line.endswith("true")
        elif line == "}":
            block = None
        else:
            m = LINE.match(line)
            if m:
                block["lines"].append((m.group("text"), m.group("kind").strip()))
            elif block["lines"]:
                # A statement whose Debug text spans several lines.
                text_, kind = block["lines"][-1]
                block["lines"][-1] = (text_ + "\n" + line, kind)
    if saw_mir and not bodies:
        raise FormatError("found `Show MIR` but no `MIR [kind] path (DefId)` headers; the log comes "
                          "from an older cargo-rapx. Install this branch with `cargo install --path rapx` "
                          f"in {ROOT}, or put {ROOT / 'target/debug'} first in PATH after `cargo build`")
    for b in bodies:
        # Cargo compiles workspace members in parallel and their stderr interleaves line by line.
        if [l["index"] for l in b["locals"]] != list(range(len(b["locals"]))) or \
                [k["index"] for k in b["blocks"]] != list(range(len(b["blocks"]))):
            raise FormatError(f"the MIR of {b['path']} is interleaved with other output; several "
                              "crates were compiled in parallel, rerun with CARGO_BUILD_JOBS=1")
    return bodies


def successors(terminator_text):
    """Normal-flow successors; unwind edges are excluded."""
    if " -> " not in terminator_text:
        return []
    targets = terminator_text.split(" -> ", 1)[1]
    return [int(m.group("bb")) for m in SUCC.finditer(targets) if m.group("label") != "unwind"]


def check_kind(text):
    for name, needles in CHECKS:
        if any(n in text for n in needles):
            return name
    return "other"


def measure(body):
    types = {l["index"]: l["ty"] for l in body["locals"]}
    stmt_kinds, term_kinds, casts, checks = Counter(), Counter(), Counter(), Counter()
    box_ptrs = set()
    for b in body["blocks"]:
        for text, kind in b["lines"]:
            if kind == "Assign(Cast)":
                dst, cast, box_deref = classify_cast(text, types)
                casts[cast] += 1
                if box_deref:
                    box_ptrs.add(dst)
    # Pointers produced by Box deref lowering are not raw-pointer use in the source.
    raw_ptrs = {i for i, ty in types.items() if ty.startswith(("*const ", "*mut "))} - box_ptrs
    calls, raw_deref_sites, indirect = [], [], 0
    statements = storage = 0
    normal = {b["index"] for b in body["blocks"] if not b["cleanup"]}
    edges = 0
    for b in body["blocks"]:
        if not b["lines"]:
            continue
        *stmts, (term_text, term_kind) = b["lines"]
        for text, kind in stmts:
            if kind in ("StorageLive", "StorageDead"):
                storage += 1
                continue
            statements += 1
            stmt_kinds[kind] += 1
        for text, _ in b["lines"]:
            raw_deref_sites += [f"bb{b['index']}: {text}"
                                for idx in DEREF.findall(text) if int(idx) in raw_ptrs]
        call = CALL.match(term_kind)
        term_kinds["Call" if term_kind.startswith("Call") else term_kind] += 1
        if call:
            calls.append(dict(callee=call.group("callee"), krate=int(call.group("krate"))))
        elif term_kind == "Call: <indirect>":
            indirect += 1
        elif term_kind == "Assert":
            checks[check_kind(term_text)] += 1
        if not b["cleanup"]:
            edges += sum(1 for s in successors(term_text) if s in normal)
    named = [l for l in body["locals"] if l["names"]]
    return dict(
        kind=body["kind"], category=category(body["kind"]), path=body["path"],
        crate=body["crate"], def_id=body["def_id"],
        locals=len(body["locals"]), named_locals=len(named),
        blocks=len(body["blocks"]), cleanup_blocks=len(body["blocks"]) - len(normal),
        cyclomatic=edges - len(normal) + 2 if normal else 0,
        statements=statements, storage_markers=storage,
        statement_kinds=dict(stmt_kinds), terminator_kinds=dict(term_kinds),
        calls=len(calls) + indirect, indirect_calls=indirect, callees=calls,
        drops=term_kinds.get("Drop", 0), runtime_checks=dict(checks),
        casts=dict(casts), raw_ptr_locals=len(raw_ptrs), raw_ptr_derefs=len(raw_deref_sites),
        raw_ptr_deref_sites=raw_deref_sites,
    )


def callee_group(call, crate):
    if call["krate"] == 0:
        return crate
    head = call["callee"].lstrip("<").split("::", 1)[0]
    return head.split(" ", 1)[0]


def summarize(metrics, top):
    crates = {}
    for crate in dict.fromkeys(m["crate"] for m in metrics):
        ms = [m for m in metrics if m["crate"] == crate]
        fns = [m for m in ms if m["category"] == "fn"]
        callees, groups = Counter(), Counter()
        for m in fns:
            for c in m["callees"]:
                callees[c["callee"]] += 1
                groups[callee_group(c, crate)] += 1

        def total(key):
            return sum(m[key] for m in fns)

        def merged(key):
            out = Counter()
            for m in fns:
                out.update(m[key])
            return dict(out.most_common())

        ranked = sorted(fns, key=lambda m: (-m["cyclomatic"], -m["blocks"], m["path"]))
        crates[crate] = dict(
            bodies=len(ms),
            by_kind=dict(Counter(m["kind"] for m in ms).most_common()),
            by_category=dict(Counter(m["category"] for m in ms).most_common()),
            fn_totals={k: total(k) for k in ("blocks", "cleanup_blocks", "statements", "calls",
                                             "indirect_calls", "drops", "raw_ptr_derefs")},
            statement_kinds=merged("statement_kinds"),
            terminator_kinds=merged("terminator_kinds"),
            casts=merged("casts"), runtime_checks=merged("runtime_checks"),
            top_complex=[pick(m, "path", "kind", "cyclomatic", "blocks", "calls") for m in ranked[:top]],
            top_callees=[dict(callee=c, count=n) for c, n in callees.most_common(top)],
            callee_crates=dict(groups.most_common()),
            raw_ptr_deref_bodies=[pick(m, "path", "raw_ptr_derefs", "raw_ptr_deref_sites")
                                  for m in fns if m["raw_ptr_derefs"]],
            transmute_bodies=[m["path"] for m in fns if m["casts"].get("Transmute")],
        )
    return crates


def pick(d, *keys):
    return {k: d[k] for k in keys}


def table(rows, headers):
    out = ["| " + " | ".join(headers) + " |", "|" + "---|" * len(headers)]
    out += ["| " + " | ".join(str(c).replace("|", "\\|") for c in row) + " |" for row in rows]
    return "\n".join(out)


def counter_line(d):
    return ", ".join(f"{k} {v}" for k, v in d.items()) or "none"


def share_line(d):
    total = sum(d.values())
    return ", ".join(f"{k} {v} ({v * 100 // total}%)" for k, v in d.items()) or "none"


def render_md(crates, toolchain):
    parts = []
    for crate, s in crates.items():
        t = s["fn_totals"]
        parts += [
            f"## MIR statistics: {crate}",
            f"- toolchain: {toolchain or 'unknown (statistics from a saved log)'}",
            f"- bodies: {s['bodies']} ({counter_line(s['by_category'])})",
            f"- body kinds: {counter_line(s['by_kind'])}",
            "- function-like totals: " + counter_line(t),
            f"- statements: {counter_line(s['statement_kinds'])}",
            f"- terminators: {counter_line(s['terminator_kinds'])}",
            f"- casts: {counter_line(s['casts'])}",
            f"- compiler-inserted runtime checks: {counter_line(s['runtime_checks'])}",
            f"- callee crates: {share_line(s['callee_crates'])}",
            "",
            "### Most complex bodies (cyclomatic complexity of the non-cleanup CFG)",
            table([(m["path"], m["kind"], m["cyclomatic"], m["blocks"], m["calls"]) for m in s["top_complex"]],
                  ["body", "kind", "cyclomatic", "blocks", "calls"]),
            "",
            "### Most frequent callees",
            table([(c["callee"], c["count"]) for c in s["top_callees"]], ["callee", "calls"]),
            "",
            "### Bodies dereferencing raw pointers",
            table([(m["path"], m["raw_ptr_derefs"], "; ".join(f"`{x}`" for x in m["raw_ptr_deref_sites"]))
                   for m in s["raw_ptr_deref_bodies"]], ["body", "derefs", "sites"])
            if s["raw_ptr_deref_bodies"] else "none",
            "",
            "### Bodies using transmute (excluding compiler-inserted ones)",
            "\n".join(f"- {p}" for p in s["transmute_bodies"]) or "none",
            "",
        ]
    return "\n".join(parts)


def repo_toolchain():
    """The toolchain this RAPx checkout builds with, which cargo-rapx must run under.

    `--run` executes cargo in the target crate, where a different default (often
    stable) would apply and cargo-rapx could not load its librustc_driver.
    """
    try:
        out = subprocess.run(["rustup", "show", "active-toolchain"], cwd=ROOT,
                             capture_output=True, text=True, check=True).stdout
    except (OSError, subprocess.CalledProcessError):
        return None
    return out.split()[0] if out.strip() else None


def run_rapx(crate_dir, toolchain):
    cmd = ["cargo"] + ([f"+{toolchain}"] if toolchain else []) + ["rapx", "analyze", "mir"]
    # One rustc at a time, otherwise the MIR of workspace members interleaves.
    env = dict(os.environ, CARGO_TERM_COLOR="never", CARGO_BUILD_JOBS="1")
    proc = subprocess.run(cmd, cwd=crate_dir, env=env, capture_output=True, text=True)
    if proc.returncode != 0:
        tail = "\n".join(proc.stderr.splitlines()[-20:])
        if "librustc_driver" in proc.stderr:
            tail += ("\nhint: cargo-rapx was built with another toolchain; "
                     "pass --toolchain with the one used to build it")
        raise SystemExit(f"`{' '.join(cmd)}` failed with exit code {proc.returncode}:\n{tail}")
    return proc.stderr


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("log", nargs="?", help="saved stderr of `cargo rapx analyze mir`, or - for stdin")
    ap.add_argument("--run", metavar="CRATE_DIR", help="run `cargo rapx analyze mir` in CRATE_DIR")
    ap.add_argument("--toolchain", help="rustup toolchain for --run, e.g. nightly-2026-10-26")
    ap.add_argument("--save-log", metavar="FILE", help="with --run, also save the raw log")
    ap.add_argument("--format", choices=["md", "json"], default="md")
    ap.add_argument("--top", type=int, default=10)
    ap.add_argument("--show", metavar="SUBSTRING", help="print the MIR of bodies whose path contains SUBSTRING")
    args = ap.parse_args(argv)

    toolchain = None
    if args.run:
        toolchain = args.toolchain or repo_toolchain()
        text = run_rapx(args.run, toolchain)
        if args.save_log:
            Path(args.save_log).write_text(text)
    elif args.log in (None, "-"):
        text = sys.stdin.read()
    else:
        text = Path(args.log).read_text(errors="replace")

    try:
        bodies = parse(text)
    except FormatError as e:
        raise SystemExit(f"error: {e}")
    if not bodies:
        raise SystemExit("error: no MIR bodies found; is this the stderr of `cargo rapx analyze mir`?")

    if args.show:
        matched = [b for b in bodies if args.show in b["path"]]
        if not matched:
            raise SystemExit(f"error: no body path contains {args.show!r}")
        print("\n\n".join("\n".join(b["text"]) for b in matched))
        return

    metrics = [measure(b) for b in bodies]
    if args.format == "json":
        print(json.dumps(dict(toolchain=toolchain, crates=summarize(metrics, args.top), bodies=metrics),
                         indent=2))
    else:
        print(render_md(summarize(metrics, args.top), toolchain))


if __name__ == "__main__":
    try:
        main()
    except BrokenPipeError:
        # The reader (e.g. `| head`) stopped early; that is not an error.
        os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())
        sys.exit(0)
