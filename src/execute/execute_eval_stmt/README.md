# `execute_eval_stmt` — `eval expr`

Exact evaluation with checked source-to-result equality publication.

## Pipeline

1. Source WD, including the full callable domain and its predicate conditions.
2. `known_closed_numeric_equal` rewrite (same index as atomic-fact rewrite).
3. Recursive `evaluate_obj`
   - `ClosedNumericExpr` → exact rational / bounded radical / closed decimal
     (includes integer-domain `% quot gcd lcm !`, foldable `sqrt` / `log`)
   - arithmetic ops → eval children → rebuild → simplify
   - plain-Identifier `FnObj` with stored algo → case dispatch → eval return
   - anonymous/named function equations → IdentifierId substitution → eval body
   - finite range/set sums and products → enumerate → checked applications → exact fold
   - checked literal finite sizes/extrema and finite-function coordinate calls → exact value
4. Verify every executed algorithm's defining equation at its normalized arguments.
5. Check the generated equality's WD and publish it through `store_fact_and_infer`.
   `exec_stmt` commits the fact only on success; proof-local eval stays local.

Nested aggregates share one allowance of 1024 terms. Endpoint count/advancement
use checked integers. Symbolic sets need an actual known enumeration for numeric
evaluation. Reversed range sums/products remain invalid; empty finite-set sum
and product return 0 and 1. No approximate number is used as equality evidence.

Equality's `AggregateCalculation` consumer shares this evaluator and retains
each application WD, function equation, argument, value and running fold.
Algorithm terms additionally require a checked stored function equation before
contributing to an equality proof. The explicit `eval` command independently
checks each finite recorded equation before publishing its exact result. It
does not enlarge implicit equality search permissions.

## Layout

| File | Owns |
|---|---|
| `exec_eval_stmt.rs` | `exec_stmt` entry + tests |
| `evaluate_obj.rs` | recursive tree walk |
| `evaluate_finite_objects.rs` | checked literal cardinality/extrema and tuple values |
| `evaluate_closed_numeric.rs` | closed-numeric simplify leaf |
| `evaluate_aggregate.rs` | bounded range/set enumeration, application and fold |
| `aggregate_evaluation_result.rs` | separate Sum/Product/set success evidence and term traces |
| `dispatch_algo.rs` | Identifier FnObj → `StoredDefAlgo` (by cases / by induc) |
| `verify_evaluated_algo_calls.rs` | Check the executed trace's mathematical defining equations |
| `helper.rs` | depth/cycle keys, arg flatten, algo param subst |
| `result.rs` | `ExecCommandStmtResult` / Failed variants |

## Tracer

`examples/stmt_nodes/command/eval.lit`
Publication, algorithms and recursion: `command/eval_store_result.lit`.
Complex nested closed trees: `command/eval_closed_numeric_complex.lit`
Range/set aggregates: `command/aggregate_eval.lit`; direct equalities and symbolic
laws: `examples/proof_nodes/equal/by_builtin_rule/aggregate_calculation.lit` and
`aggregate_identities.lit`.

## Literal finite objects (example small repairs)

`eval finite_set_size({1,2,3})` uses source WD before computing. Finite
extrema require a nonempty finite real set; literal fractions are compared
exactly by the sign of a normalized rational difference. Empty extrema and
nonreal elements reject.

Finite tuples use ordinary one-based function application. After
`let p=(1,2,3)`, `eval p(2)` computes `2` and publishes `p(2)=2` without an
earlier coordinate assertion. After
`have outer cart(cart(R,R),R)=((1,2),3)`, `eval outer(1)(2)` follows the
checked coordinate beta steps. `let literal_outer=((1,2),3)` likewise
supports `eval literal_outer(1)(2)` through its checked prefix value. Each step retains its actual value/member
source and application WD in `function_evaluations`; aggregates consuming this
evaluator retain the same evidence. A carrier alone does not determine a
value: `have unknown cart(R,R); eval unknown(1)` declines evaluation.
Out-of-domain calls and scalar continuation fail WD before publication.

Acceptance: `examples/stmt_nodes/command/eval_finite_function_coordinate.lit`;
`examples/proof_nodes/equal/by_object_definition/by_fn_application/nested_tuple_coordinate_call.lit`.
Retired `tuple_dim` and bracket indexing remain rejected.


## Exact signed powers and numeric complex modulus

Closed numeric integer powers use a checked reciprocal for a negative exponent;
source WD requires a nonzero base. Exact nonterminating fractions remain
rational objects. Numeric `C_abs` shares the pure coordinate calculator with
the equality rule, accepts reordered and signed coordinates, and displays the
nonnegative principal root (an exact `sqrt` when nonsquare), and the command
stores the corresponding equality. Inputs outside the numeric coordinate grammar or checked integer
bounds decline calculation. Periodic trig values belong to equality/WD rules;
this display evaluator does not independently execute symbolic trig functions.

Tracers: `examples/proof_nodes/equal/by_builtin_rule/negative_integer_power_exact.lit`
and `numeric_complex_modulus.lit`. Boundary tests:
`tests/unit/execute/exact_numeric_periodic_modulus/tests.rs`.

## Closed elementary calculations

Closed positive rational bases with reduced rational exponent `p/q` use
`exact_rational`: take exact integer roots of both base components before the
checked integer power. Thus `eval 8^(1/3)` displays `2`, and
`eval (4/9)^(1/2)` displays `2 / 3`. Pow source WD separately checks closed
`Q+`/`Q` inputs; it does not depend on a rational output. Nonperfect roots and
overflow decline evaluation. Existing integer domains are unchanged, and
nonpositive bases with noninteger exponents remain unsupported.
Tracer: `examples/proof_nodes/equal/by_builtin_rule/closed_rational_power_calculation.lit`;
regression/collector: `tests/unit/execute/exact_rational_powers/tests.rs`.

Fraction rounding and sign, integer-valued rational operands, perfect rational
square roots and rational logarithms use `exact_rational`. `exact_radical`
normalizes bounded rational linear combinations of square-free roots, products,
integer powers and single-term radical denominators. `exact_complex` supplies
closed rational-coordinate arithmetic and `re`/`img` projections.
For example, `eval floor(-7/3)` displays `-3`, `eval sqrt(12)+sqrt(27)` displays
`5 * sqrt(3)`, and `eval log(8,4)` displays `2 / 3`. Their assertion counterparts
use the same pure producers at the central closed-calculation leaf.

Source WD remains first. The pure computation leaf never uses approximate
logs/roots, stores a fact, or calls a premise verifier; `exec_eval_stmt` owns
the checked publication. Factorization above trial divisor 10,000,
checked-integer overflow, radical expressions exceeding 64 terms/levels and
general sums in radical denominators decline this calculator.
Tracers: `closed_fraction_rounding_calculation.lit`,
`closed_radical_calculation.lit`, `closed_complex_parts_calculation.lit`,
`closed_rational_log_calculation.lit` under
`examples/proof_nodes/equal/by_builtin_rule/`; controls under
`examples/negative/closed_exact_elementary_calculation/`.
