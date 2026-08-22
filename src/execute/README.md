# Executing statements

For `1 + 1 = 2`, execution checks the expression, verifies the equality, stores the fact, and attaches a statement trace.

```text
exec_stmt(Stmt::Fact(1 + 1 = 2))
  clear statement-local proof caches
  verify both sides are well-defined
  verify 1 + 1 = 2
  store the fact and allocate its FactId
  run inference from the stored fact
  attach proof FactIds and execution phases
  return StmtResult::Success
```

## Examples and boundaries

| Statement | Execution behavior |
| --- | --- |
| `1 + 1 = 2` | Uses verified execution and stores the successful fact. |
| `have a R = 1` | Creates an object definition only after its required facts verify. |
| `try:`<br>&nbsp;&nbsp;`1 = 2` | Rolls back the failed block instead of committing its environment changes. |
| `trust 1 = 2` | Uses the unsafe statement path; `-strict` rejects this example. |
| A failed `1 / 0 = 0` | Stops after well-definedness; verification and environment mutation do not run. |

## Start here

| File | Example |
| --- | --- |
| [`exec_stmt.rs`](exec_stmt.rs) | Dispatches every `Stmt` and attaches the final execution trace. |
| [`exec_fact_stmt.rs`](exec_fact_stmt.rs) | Executes a submitted fact such as `1 + 1 = 2`. |
| [`exec_verify_then_store_facts.rs`](exec_verify_then_store_facts.rs) | Implements verify-then-store for facts. |
| [`exec_try_stmt.rs`](exec_try_stmt.rs) | Gives `try:` its transactional rollback behavior. |
