# Result and dependency graphs

`litex -graph -e '1 = 1' graph.json` turns the checked result for `1 = 1` into graph JSON with proof and dependency nodes.

```text
run source `1 = 1`
  -> collect StmtResult and RuntimeError
  -> visit recursive proof/well-definedness Results
  -> preserve shared nodes with references
  -> emit graph metadata, nodes, and edges
```

## Examples and boundaries

| Command | Graph |
| --- | --- |
| `litex -graph -e '1 = 1' graph.json` | Recursive result/proof/FactId graph. |
| `litex -factgraph -e '1 = 1' facts.json` | Fact-only dependency graph. |
| `litex -defgraph -f chapter.lit defs.json` | Environment-backed definition dependency graph. |
| A failed `1 / 0 = 0` graph run | Includes the structured error instead of inventing a successful proof node. |
| Two proof branches sharing one Result | Emit one shared node plus references, not duplicated independent proofs. |

The three graph concepts have separate directories:

| Directory | Ownership boundary |
| --- | --- |
| [`result_graph/`](result_graph) | Result, proof, well-definedness, and inference nodes and edges. |
| [`fact_graph/`](fact_graph) | Stored-fact dependency collection and source resolution. |
| [`definition_graph/`](definition_graph) | Definition inventory, dependency analysis, provenance, and rendering. |

Within each directory, `model.rs` owns graph data, `entrypoints.rs` or
`construction.rs` starts the operation, and the narrower node/edge/rendering
files own their named responsibilities. Command execution remains outside the
graph models in [`graph_execution.rs`](graph_execution.rs),
[`result_graph_execution.rs`](result_graph_execution.rs), and
[`../pipeline/output_rendering.rs`](../pipeline/output_rendering.rs).
