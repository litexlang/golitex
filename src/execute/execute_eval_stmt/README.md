# `execute_eval_stmt` — `eval expr`

Display evaluation only (no proof fact stored).

## Pipeline

1. Source WD, including the full callable domain and its predicate conditions.
2. `known_closed_numeric_equal` rewrite (same index as atomic-fact rewrite).
3. Recursive `evaluate_obj`
   - `ClosedNumericExpr` → exact rational / closed decimal
     (includes integer-domain `% quot gcd lcm !`, foldable `sqrt` / `log`)
   - arithmetic ops → eval children → rebuild → simplify
   - plain-Identifier `FnObj` with stored algo → case dispatch → eval return
   - anonymous/named function equations → IdentifierId substitution → eval body
   - finite range/set sums and products → enumerate → checked applications → exact fold

Nested aggregates share one allowance of 1024 terms. Endpoint count/advancement
use checked integers. Symbolic sets need an actual known enumeration for numeric
evaluation. Reversed range sums/products remain invalid; empty finite-set sum
and product return 0 and 1. No approximate number is used as equality evidence.

Equality's `AggregateCalculation` consumer shares this evaluator and retains
each application WD, function equation, argument, value and running fold.
Algorithm terms additionally require a checked stored function equation before
contributing to an equality proof. Display evaluation publishes no equality.

## Layout

| File | Owns |
|---|---|
| `exec_eval_stmt.rs` | `exec_stmt` entry + tests |
| `evaluate_obj.rs` | recursive tree walk |
| `evaluate_closed_numeric.rs` | closed-numeric simplify leaf |
| `evaluate_aggregate.rs` | bounded range/set enumeration, application and fold |
| `aggregate_evaluation_result.rs` | separate Sum/Product/set success evidence and term traces |
| `dispatch_algo.rs` | Identifier FnObj → `StoredDefAlgo` (by cases / by induc) |
| `helper.rs` | depth/cycle keys, arg flatten, algo param subst |
| `result.rs` | `ExecCommandStmtResult` / Failed variants |

## Tracer

`examples/stmt_nodes/command/eval.lit`
Complex nested closed trees: `command/eval_closed_numeric_complex.lit`
Range/set aggregates: `command/aggregate_eval.lit`; direct equalities and symbolic
laws: `examples/proof_nodes/equal/by_builtin_rule/aggregate_calculation.lit` and
`aggregate_identities.lit`.
