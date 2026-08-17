# Compiler2 examples

This directory is the canonical ledger for examples targeting the
`litex_to_lean_compiler2` ABI. It must not import or depend on the archived
universal-`Litex.Object` ABI.

Run the complete compiler2 Lean gate from the compiler2 repository:

```sh
cd lean
lake build
```

Run one example directly in the same environment:

```sh
cd lean
lake env lean examples/SetSystem.lean
```

`SetSystem.lean` is the tracer for `Same`, `Set`, heterogeneous `In`, native
numeric sets, user-defined exact-carrier and predicate sets, and a universe-1
set whose elements are universe-0 Litex sets.

`OrderSystem.lean` is the tracer for `AsReal`, heterogeneous `Lt`/`Le`, the
source rule `a < b => a <= b`, and the explicit `RealCoherence` boundary used
when a theorem must identify two real representatives. Function compilation is
intentionally deferred.
