---
name: rapx-mir
description: Run RAPx mir / dot-mir to dump the MIR of every body in a Rust crate, then use tools/mir/mir_stats.py to get per-body and crate-level statistics (CFG size, cyclomatic complexity, calls, drops, raw-pointer derefs, casts, compiler-inserted runtime checks) or the MIR of one function. Applies to inspecting and measuring MIR only, not bug detection, verification verdicts, or optimization advice.
---

# RAPx mir

## When to use

- To see the real control flow of a function after lowering: where drops are inserted, which
  path unwinding takes, what `?`, `match` and loops become, and which functions are called.
  Extract that function's MIR with `--show` first, then read it.
- To build a MIR-level profile of a crate: how many bodies it has, which functions are the most
  complex, which APIs are called most, and which functions dereference raw pointers or use
  transmute. Get the numbers from `mir_stats.py`; do not count by hand.
- To check the MIR evidence at the location of a warning when explaining the result of another
  RAPx check (safedrop, rcanary, opt).
- To draw CFG graphs (for reports or explanations), use `dot-mir`.

The MIR of a real crate easily runs to tens or hundreds of thousands of lines (about 180k for
regex-syntax). Do not read the full output into context: leave the statistics to the script and
read only the specific functions you need.

## Prerequisites

The cargo-rapx on `PATH` must be built from this branch. Older versions do not print the
`MIR [kind]` headers, and the script then reports `the log comes from an older cargo-rapx`. When
this happens, do not reinstall on your own: `cargo install --path rapx` replaces the user's global
rapx and cargo-rapx, so ask the user first. The alternative is to run `cargo build -p rapx` in the
RAPx repository and put `<RAPx>/target/debug` first in `PATH` for that command only.

## Usage

Run from the root of the RAPx repository (`CRATE_DIR` is the root of the crate to analyze):

```shell
# Crate-wide statistics in Markdown; --format json gives the full metrics of every body
python3 tools/mir/mir_stats.py --run CRATE_DIR --save-log /tmp/mir.log --top 10
# Query the same log again later without recompiling
python3 tools/mir/mir_stats.py /tmp/mir.log --format json
python3 tools/mir/mir_stats.py /tmp/mir.log --show 'Buf::push'   # MIR of bodies whose path contains the string
```

`--run` executes `cargo +<toolchain> rapx analyze mir` in `CRATE_DIR`. `<toolchain>` defaults to
the toolchain active in the RAPx repository (`rustup show active-toolchain`), not the default of
the target crate's directory; otherwise cargo-rapx fails to load `librustc_driver-*.so`. Pass
`--toolchain` only when cargo-rapx was built with a different toolchain. Do not work around this
by setting `LD_LIBRARY_PATH`. The first line of the report states the toolchain actually used.

The commands can also be run directly; their output goes to stderr only:

```shell
CARGO_BUILD_JOBS=1 cargo +<toolchain> rapx analyze mir 2> mir.log
cargo rapx analyze dot-mir     # writes MIR_dot_graph/<path>.png in the crate root
```

`CARGO_BUILD_JOBS=1` is required: cargo compiles workspace members in parallel and their stderr
interleaves line by line, mixing up the MIR. `--run` sets it automatically, and the script reports
an error on an interleaved log instead of producing wrong statistics.

`dot-mir` needs Graphviz's `dot`. Without it, it prints a warning and keeps
`MIR_dot_graph/<path>.dot` so the graph can be rendered later.

## Implementation

`rapx/src/helpers/show_mir.rs` iterates over `tcx.mir_keys(())`, i.e. every body with MIR in the
local crate, and prints `tcx.instance_mir(InstanceKind::Item(def_id))` for each one. The functions
RAPx injects itself, `__raw_ptr_deref_dummy` and `__static_mut_deref_dummy`, are skipped. RAPx
compiles with `-Zmir-opt-level=0`, so the result is lowered but unoptimized MIR: drops have been
elaborated, `StorageLive/Dead` and cleanup blocks are kept, and nothing is inlined. `dot-mir`
generates DOT for the same bodies and highlights basic blocks that contain drops in red.

## Output format

Each body is printed in three parts, each prefixed with `HH:MM:SS|RAPx|INFO|: `:

```
MIR [method] Buf::push (DefId(0:9 ~ mir_demo[72e4]::{impl#0}::push))
_0: bool
_1: &mut Buf @ self
_2: u8 @ b
bb 0 {
CleanUp: false
    _6 = &((*_1).0: std::vec::Vec<u8>) @ Assign(Ref)
    _5 = std::vec::Vec::<u8>::len(move _6) -> [return: bb1, unwind continue] @ Call: std::vec::Vec::<T, A>::len #3:9869
}
```

- Header: `MIR [kind] path (DefId)`. The kind comes from rustc's `def_descr`: `function`,
  `method`, `associated_function`, `closure`, `async_fn` (the async body; the outer `fn` only
  builds the future), `constant`, `static`, `associated_constant`, `constant_expression` (such as
  the length in `[0; 4]`), `tuple_variant`/`tuple_struct` (constructors), and so on.
- Locals: `_i: type`. `_0` is the return value and `_1.._n` are the arguments; locals with a name
  in the source get ` @ name` appended.
- Basic blocks: `CleanUp: true` marks an unwind cleanup block. Each line is `MIR statement @ kind`,
  and the last line is the terminator. Statement kinds are `Assign(rvalue kind)`, `StorageLive`,
  `SetDiscriminant` and so on; terminator kinds are `Goto`, `SwitchInt`, `Return`, `Drop`,
  `Assert`, `UnwindResume` and so on. Unrecognized kinds are printed as `Other`.
- Calls: `Call: <callee def path> #<crate number>:<index>`, where crate number 0 is the local
  crate; a call through a function pointer is `Call: <indirect>`. The callee is the definition
  path: a trait method shows as `std::iter::Iterator::next`, and the implementing type is in the
  statement text on the same line, `<X as Trait>::next`. Calls on `dyn Trait` also show the trait
  method (for example `Call: T::m`), since virtual dispatch is resolved after MIR.

## Metrics (mir_stats.py)

Results are grouped by crate. Bodies fall into three categories, `fn`, `const` and `ctor`; rankings
and totals count `fn` bodies only.

- `blocks`/`cleanup_blocks`: the number of basic blocks, and how many of them are cleanup blocks.
- `cyclomatic`: E − N + 2 on the CFG of non-cleanup blocks without unwind edges, approximating
  the branching complexity of the source.
- `statements`: statements excluding `StorageLive/Dead`; counts by kind are in `statement_kinds`.
- `calls`/`indirect_calls`/`callees`: call sites and their callees. `callee_crates` groups callees
  by the first segment of their path (`std`, `core`, the crate's own name, ...). std re-exports
  show as `std::` even when defined in alloc or core.
- `drops`: the number of `Drop` terminators, including those in cleanup blocks.
- `raw_ptr_derefs`/`raw_ptr_deref_sites`: the number of derefs `(*_k)` of locals with raw-pointer
  type, and the `bbN: statement` of each one; pointers produced by lowering `*box` are excluded.
  Cite these sites when checking; do not grep for `(*_`, which also matches derefs of references.
- `casts`: counts by cast kind. `Transmute(compiler)` and `BoxDerefTransmute` are generated by the
  compiler (Box derefs, null and alignment checks, the resume argument of async bodies); only
  `Transmute` is a transmute in the source.
- `runtime_checks`: `Assert` terminators by message: `overflow`, `bounds`, `div_by_zero`,
  `null_deref`, `misaligned`, `coroutine_resume`, `other`. These checks come from the debug
  assertions of the dev profile, not from the user's `assert!` (which is a call to a panic
  function).

## Caveats when interpreting

- Only the local crate is covered, not its dependencies. Each workspace member forms its own group.
- MIR is polymorphic, not monomorphized: a generic function appears once, and callee paths keep
  parameters such as `<T, A>`.
- Closures, async bodies and anonymous constants are separate bodies; when measuring a source
  function, include its `::{closure#N}` bodies.
- `raw_ptr_derefs` counts direct derefs such as `(*p)` only. Operations done through unsafe APIs
  such as `ptr::read/write/add/copy_nonoverlapping` or `set_len` appear as calls; look at
  `top_callees` or `callees` in `--format json` for them. A low deref count alone does not mean
  little unsafe code is used.
- To compare call shares between crates, use the percentages after `callee crates`; do not infer
  the overall picture from the top few callees.
- Telling `Transmute(compiler)` and Box derefs apart relies on matching type patterns and is a
  heuristic; before drawing a conclusion about a specific function, check the MIR with `--show`.
- The numbers change with the rustc version (lowering changes), so compare two results only when
  they were produced with the same toolchain.

## Reporting

Give the crate name, the toolchain used, the total number of bodies and the split into the three
categories, the `fn` totals, the N most complex functions, the most frequent callees, and the
functions with raw-pointer derefs and user transmutes. Then give a short interpretation based on
these numbers, such as where the complexity concentrates and in which modules unsafe-related
operations occur. When citing a specific function, include the key lines of its MIR from `--show`
as evidence, and cite raw-pointer derefs by the sites in `raw_ptr_deref_sites`. All numbers must
come from the script, never from manual estimates. Mark any interpretation that was not checked
case by case as an inference.
