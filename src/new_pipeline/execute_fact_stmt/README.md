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
The new pipeline owns its runtime IDs in `runtime::runtime_ids`.
`runtime::runtime_ids::FactId` is intentionally independent from the legacy
`fact::id::FactId`; compatibility, if needed later, must be explicit.
New verifier types/fns use a `2` suffix (e.g. VerifyFactResult2, verify_fact2)
```

This keeps FactIds and temporary environments compatible with later Lean
consumers while the new Result and pipeline shapes are still being drafted.
