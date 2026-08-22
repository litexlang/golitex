# Mathematical facts

`1 = 1` and `1 = 1 and 2 = 2` differ from this universal fact:

```litex
forall x R:
    x = x
```

## Examples and boundaries

| Litex fact | Rust shape |
| --- | --- |
| `1 = 1` | `Fact::AtomicFact(EqualFact(...))`. |
| `1 != 2` | A negated atomic equality fact. |
| `1 = 1 and 2 = 2` | `Fact::AndFact`; inference can store both components. |
| `1 = 1 or 1 = 2` | `Fact::OrFact`. |
| `1 = 1 = 1` | `Fact::ChainFact`. |
| The `forall x R:` example above | `Fact::ForallFact`. |
| `exist x R st {x = 0}` | `Fact::ExistFact`. |

[`fact.rs`](fact.rs) owns the top-level variants; for example, [`forall_fact.rs`](forall_fact.rs) stores the binder and body of the universal above, while [`atomic_fact.rs`](atomic_fact.rs) stores `1 = 1`.
