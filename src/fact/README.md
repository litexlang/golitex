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

`AtomicFact::has_positive_polarity()` distinguishes a positive atomic form
such as `x = y` from its negative counterpart `x != y`. It does not claim that
the proposition has been verified; verification success belongs to
`StmtResult::is_success()`.

[`types.rs`](types.rs) owns the top-level `Fact` variants. The implementation is
then grouped by mathematical shape:

- [`atomic/`](atomic/) owns atomic representation, arguments, conversions, and
  predicate metadata such as the `1 = 1` example.
- [`composite/`](composite/) owns conjunctions, disjunctions, relation chains,
  their order closure, and quantifier-free fact bodies.
- [`quantified/`](quantified/) owns existential and universal binders, nested
  bodies, iff universals, and parameter coverage.
- [`validation/`](validation/) owns duplicate free-parameter checks for facts
  and binder-owning objects.

`mod.rs` preserves the flat public API, so consumers continue to import
`litex::fact::{Fact, ForallFact, AtomicFact, ...}`.
