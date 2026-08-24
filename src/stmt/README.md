# Executable statements

`1 = 1` is a fact statement, `have a R = 1` is an object-definition statement, and `claim:` starts a proof-block statement.

## Examples and boundaries

| Litex statement | `Stmt` family |
| --- | --- |
| `1 = 1` | `Stmt::Fact`. |
| `have a R = 1` | `Stmt::DefObjStmt`. |
| `prop is_one(x R):`<br>&nbsp;&nbsp;`x = 1` | `Stmt::DefPredicateStmt`. |
| `thm one_eq_one:`<br>&nbsp;&nbsp;`? forall:`<br>&nbsp;&nbsp;&nbsp;&nbsp;`1 = 1` | `Stmt::DefThmStmt`. |
| `by contra:`<br>&nbsp;&nbsp;`? 1 = 1`<br>&nbsp;&nbsp;`impossible 1 != 1` | `Stmt::By`. |
| `witness exist x R st {x = 1} from 1:`<br>&nbsp;&nbsp;`1 = 1` | `Stmt::Witness`. |
| `claim:`<br>&nbsp;&nbsp;`? 1 = 1`<br>&nbsp;&nbsp;`1 = 1` | `Stmt::ProofBlock`. |
| `eval 1 + 1` | `Stmt::Command`. |
| `trust 1 = 2` | `Stmt::UnsafeStmt`; strict execution rejects this example. |

Start with [`statement_types.rs`](statement_types.rs); for example, its `Stmt`
enum is the exact dispatch surface consumed by
`execute/verified_statement_execution.rs`.
