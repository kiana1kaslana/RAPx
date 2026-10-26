# Terminator counterexamples

`unsound_tail_call` uses `TailCall` to call an unsafe function with a false
`ValidNum` precondition. The `tail_call_unsafe_checkpoint` test checks constant,
symbolic, and guarded arguments at the tail-call checkpoint. It also checks a
tail-call helper's return value and write effect. Calls through unsafe function
pointers are reported as `UNKNOWN` because the callee cannot be resolved.

`make_coroutine` generates `Yield` and `CoroutineDrop` in the compiler's
pre-lowering coroutine MIR. Both are lowered away before the `optimized_mir`
that RAPx verifies, so this fixture does not treat them as reachable VM cases.
The lowered coroutine MIR still contains `SetDiscriminant` statements for its
state transitions. RAPx currently treats those as unsupported when they are
relevant to a proof.
