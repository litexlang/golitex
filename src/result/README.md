# Statement results and proof evidence

For `1 + 1 = 2`, the result is not only `true`; it retains the statement, calculation evidence, well-definedness result, FactId, inference output, and execution phases.

```text
StmtResult::Success(
  Fact {
    statement: 1 + 1 = 2,
    proof: BuiltinRule(RationalNormalization(...)),
    well_definedness: Success(...),
    fact_id: f1,
    infers: ...,
    execution_trace: Success
  }
)
```

## Examples and boundaries

| Execution | Result shape |
| --- | --- |
| `1 + 1 = 2` | `StmtResult::Success(SuccessStmtResult::Fact(...))`. |
| An unsupported fact such as a missing symbolic-power rule | `StmtResult::Unknown(...)`, not a fabricated proof. |
| `trust 1 = 2` | A distinct trusted/unsafe success result, not ordinary checked evidence. |
| `1 / 0 = 0` | A `RuntimeError` with failed well-definedness phases, not `StmtResult::Success`. |
| Reusing an earlier fact | A citation result retains the exact source `FactId`, for example `f3`. |

`StmtResult::is_success()` answers whether execution produced the `Success`
variant. It deliberately uses outcome vocabulary: mathematical polarity belongs
to `AtomicFact`, not to a statement execution result.

## Start here

| Responsibility | Start file | Example |
| --- | --- | --- |
| Statement outcome | [`statement/result.rs`](statement/result.rs) | Defines canonical `Success` versus `Unknown`. |
| Successful statements | [`statement/success.rs`](statement/success.rs) | Retains statement-specific fields and proof evidence. |
| Result navigation | [`statement/traversal.rs`](statement/traversal.rs) | Traverses and consumes recursive statement-result children. |
| Verification evidence | [`verification/success.rs`](verification/success.rs) | Defines citations, forall instantiations, cases, induction, and other checked proof routes. |
| Evidence access | [`verification/success_access.rs`](verification/success_access.rs) | Constructs and inspects proof routes without mixing behavior into their definitions. |
| Builtin rules | [`verification/builtin_evidence.rs`](verification/builtin_evidence.rs) | Represents evidence such as `RationalNormalization` and `ComplexAlgebraicNormalization`. |
| Well-definedness | [`well_definedness/proof.rs`](well_definedness/proof.rs) | Records why an expression such as `x / 2` is well-defined. |
| Object evaluation | [`object_evaluation.rs`](object_evaluation.rs) | Records literal, unary, binary, and shape evaluation steps. |

`mod.rs` keeps the established public surface flat: consumers continue to use
`litex::result::{StmtResult, SuccessStmtResult, ...}` rather than depending on
these private responsibility directories.
