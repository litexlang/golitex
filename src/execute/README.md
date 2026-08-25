# Executing statements

For `1 + 1 = 2`, execution checks the expression, verifies the equality, stores the fact, and attaches a statement trace.

```text
execute_statement(Stmt::Fact(1 + 1 = 2))
  clear statement-local proof caches
  read ExecutionMode::Verified or ExecutionMode::Trusted
  verify both sides are well-defined
  verify 1 + 1 = 2
  store the fact and allocate its FactId
  run inference from the stored fact
  attach proof FactIds and execution phases
  return StmtResult::Success
```

`ExecutionMode` says whether the current source is verified or trusted.
`StatementExecutionContext` separately says whether this statement belongs to
an ordinary run or a trusted-prefix run. Keeping those two axes named prevents
the executor from threading unexplained `true` and `false` values through the
statement lifecycle.

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
| [`statement_execution.rs`](statement_execution.rs) | Owns statement lifecycle, chooses verified or trusted execution, and attaches the final execution trace. |
| [`verified_statement_execution.rs`](verified_statement_execution.rs) | Dispatches every verified `Stmt` family to its executor. |
| [`trusted_statement_execution.rs`](trusted_statement_execution.rs) | Replays trusted and preverified statements into the environment. |
| [`attach_fact_ids_to_stmt_result.rs`](attach_fact_ids_to_stmt_result.rs) | Fills missing FactIds in the completed recursive Result tree without retargeting frozen local evidence. |
| [`submitted_fact_execution.rs`](submitted_fact_execution.rs) | Executes a submitted fact through well-definedness, proof verification, storage, and inference. |
| [`definition_execution/object/`](definition_execution/object/) | Executes object, function, tuple, sequence, matrix, preimage, and existential-elimination definitions and bindings. |
| [`witness_execution.rs`](witness_execution.rs) | Executes logical witness statements; witness introduction remains separate from definition storage. |
| [`definition_execution/`](definition_execution/) | Groups proposition, theorem, axiom, template, structure, algorithm, parameter, and definition-storage execution. |
| [`proof_block_execution/`](proof_block_execution/) | Groups claim, goal-proof, sketch, and transactional `try` execution. |
| [`command_execution/`](command_execution/) | Groups evaluation and environment commands such as `clear`. |
| [`trust_execution/`](trust_execution/) | Groups explicit unsafe fact and parameterized assumptions. |
| [`strategy_execution.rs`](strategy_execution.rs) | Defines, applies, and stops proof strategies. |
| [`verified_fact_storage.rs`](verified_fact_storage.rs) | Verifies fact well-definedness before storage and inference. |
| [`proof_block_execution/try_block.rs`](proof_block_execution/try_block.rs) | Gives `try:` its transactional rollback behavior. |
