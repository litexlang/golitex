# Inference after storing facts

Storing `1 = 1 and 2 = 2` also stores `1 = 1` and `2 = 2`, each with typed `ConjunctionImpliesComponent` inference evidence.

```text
infer(1 = 1 and 2 = 2)
  dispatch AndFact
  for each component:
    create ConjunctionImpliesComponent rule application
    cite the conjunction FactId
    store the component with its own FactId
    recursively infer from that component
```

## Examples and boundaries

| Stored fact | Derived fact example |
| --- | --- |
| `A $subset B` | A registered subset rule may produce elementwise membership consequences. |
| `x $in R+` | Produces `x > 0`, and the positive/nonzero consequences recorded by the numeric rules. |
| `a = b` and `a $in S` | Can transport membership to `b $in S` through known equality. |
| `1 = 1 and 2 = 2` | Produces the two component facts with exact source and conclusion FactIds. |
| A fact with no registered inference rule | Stores only itself; for example, an unrelated custom atomic predicate does not generate arbitrary facts. |

Start with [`dispatch.rs`](dispatch.rs) for fact-shape dispatch and [`result.rs`](result.rs) for typed rule applications such as `ConjunctionImpliesComponent`.
