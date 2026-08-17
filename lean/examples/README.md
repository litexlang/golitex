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

`SetSystem.lean` is the current tracer for `Same`, `Set`, heterogeneous `In`,
the native numeric sets, and user-defined exact-carrier and predicate sets.
Function compilation is intentionally deferred.
