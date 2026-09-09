# Staged verifier draft

`src/verify` is the in-tree draft of the verifier rewrite. It uses the
canonical fact, environment, runtime, and identifier types from the rest of
the crate, but it is exposed under `litex::verify_rewrite` so it does not take
ownership of the running verifier yet.

The compatibility path remains `litex::verify`, backed by
`litex::verification`. Result and pipeline files in this directory can be
developed in parallel; they are added to the draft module as their runtime
ownership is migrated, rather than compiling a second set of `Runtime`
methods at the same time.

The foundational correspondence is intentional:

```text
verify_rewrite uses fact::Fact / ExistFact / PlainExistFact directly
verify_rewrite::FactId   == fact::id::FactId
verify_rewrite::Environment == environment::Environment
verify_rewrite::Runtime  == runtime::Runtime
New verifier types/fns use a `2` suffix (e.g. VerifyFactResult2, verify_fact2)
```

This keeps FactIds and temporary environments compatible with later Lean
consumers while the new Result and pipeline shapes are still being drafted.
