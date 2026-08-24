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

## Start here

| File | Example |
| --- | --- |
| [`stmt_result.rs`](stmt_result.rs) | Defines `Success` versus `Unknown`. |
| [`success_stmt_result.rs`](success_stmt_result.rs) | Defines the successful statement-result variants and their retained evidence fields. |
| [`success_stmt_result_traversal.rs`](success_stmt_result_traversal.rs) | Traverses, accesses, and consumes recursive children in the successful result tree. |
| [`runtime_success.rs`](runtime_success.rs) | Defines citations, forall instantiations, cases, induction, and other checked proof-route evidence. |
| [`runtime_success_access.rs`](runtime_success_access.rs) | Constructs and inspects those proof routes without mixing their behavior into the evidence declarations. |
| [`builtin_rule_evidence.rs`](builtin_rule_evidence.rs) | Represents evidence such as `RationalNormalization` and `ComplexAlgebraicNormalization`. |
| [`well_definedness_proof.rs`](well_definedness_proof.rs) | Records why an expression such as `x / 2` is well-defined. |
