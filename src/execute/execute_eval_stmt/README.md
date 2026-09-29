# `execute_eval_stmt` — `eval expr`

Display evaluation only (no proof fact stored).

## Pipeline

1. `known_closed_numeric_equal` rewrite (same index as atomic-fact rewrite)
2. Recursive `evaluate_obj`
   - `ClosedNumericExpr` → exact rational / closed decimal
     (includes integer-domain `% quot gcd lcm !`, foldable `sqrt` / `log`)
   - arithmetic ops → eval children → rebuild → simplify
   - plain-Identifier `FnObj` with stored algo → case dispatch → eval return

## Layout

| File | Owns |
|---|---|
| `exec_eval_stmt.rs` | `exec_stmt` entry + tests |
| `evaluate_obj.rs` | recursive tree walk |
| `evaluate_closed_numeric.rs` | closed-numeric simplify leaf |
| `dispatch_algo.rs` | Identifier FnObj → `StoredDefAlgo` (by cases / by induc) |
| `helper.rs` | depth/cycle keys, arg flatten, algo param subst |
| `result.rs` | `ExecCommandStmtResult` / Failed variants |

## Tracer

`examples/stmt_nodes/command/eval.lit`
Complex nested closed trees: `command/eval_closed_numeric_complex.lit`
