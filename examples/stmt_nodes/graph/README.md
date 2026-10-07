# Mathematical dependency output

`math_dependencies.lit` exercises recorded definitions, verified facts and a
reused theorem. `by thm` and other proof commands are edge source details,
never mathematical nodes. Inferred and local facts remain available but are
folded by default in the viewer.

```sh
target/release/litex -graph -strict -f examples/stmt_nodes/graph/math_dependencies.lit > graph.json
```

Open `docs/assets/math_graph_viewer.html` and select the emitted JSON. The paired
`math_dependencies.html` is a generated, standalone preview of this fixture.
The JSON schema uses run-local IDs; it is not the legacy result graph ABI.

Producer/consumer, failure, scope, trust, citation and CLI checks live in
`src/graph/tests.rs`. Graph capture reads typed evidence and accepted
declarations before the runner's existing finish/abort operations. It does
not rerun proof search or modify verifier state.

See [the acceptance record](acceptance-2026-10-07.md) for the checks and current
verification limits.
