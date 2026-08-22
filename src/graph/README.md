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

Start with [`result_graph.rs`](result_graph.rs) for the main graph and [`fact_graph.rs`](fact_graph.rs) / [`definition_graph.rs`](definition_graph.rs) for the two specialized examples.

