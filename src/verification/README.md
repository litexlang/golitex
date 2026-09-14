# Verifying facts

`1 + 1 = 2` succeeds by calculation, while this input fails before verification because `x` may be zero:

```litex
forall x R:
    x ^ 2 / x = x
```

```text
execute_submitted_fact(1 + 1 = 2)
  verify_fact_well_defined_for_execution(1 + 1 = 2)
  verify_fact_or_error(1 + 1 = 2, VerifyState::initial())
    verify_fact_allow_unknown(1 + 1 = 2)
    dispatch EqualFact
    try closed numeric evaluation
    record RationalNormalization evidence
  store_executed_fact_and_infer(1 + 1 = 2)
  return SuccessFactStmtResult
```

## Examples and boundaries

| Goal | Verification route or boundary |
| --- | --- |
| `1 + 1 = 2` | Closed numeric calculation. |
| `(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2` | Rational-expression normalization. |
| `2 * i + 1 = i * i + 2 + 2 * i` | Complex algebraic normalization with typed evidence. |
| Store `forall x R:` / `x = x`, then check its instance `1 = 1` | The candidate matches because `1 $in R` and its body becomes `1 = 1`. |
| The division example above | Rejected as ill-defined without `x != 0`; the verifier does not invent that premise. |
| A true but unsupported identity | Returns unknown or a verification error; for example, symbolic expansion of `(x + 1) ^ n` is not supplied by rational normalization. |

## Important order

```text
well-definedness
  -> direct known facts and equalities
  -> bounded builtin rules and strategies
  -> known forall facts
  -> explicit proof syntax (`by`, witnesses, cases, induction)
  -> unknown if no checked route closes the goal
```

The order above is observable in `1 / 0 = 0`: well-definedness rejects the divisor before any equality rule runs.

`VerifyState` names the recursion boundary explicitly. `initial()` is the
ordinary outer proof search, `after_well_definedness()` prevents a child from
rechecking an already discharged gate, and `final_round()` selects the bounded
last retry. `BuiltinRuleSearchState` separately limits recursive builtin-rule
application; it is not the general proof-search state.

Atomic-family entry points named `with_bounded_builtin_routes` first try their
zero-premise leaves and may then spend one bounded builtin-rule step. For
atomic-except-equality fallback, `AlternateFactSearch::Enabled` means that order-dual
and registered symmetric alternatives may be tried; recursive alternatives use
`Disabled` so they cannot select themselves again. Checked function-definition
reduction similarly uses `EqualitySide::{Left, Right}` internally and converts
to the retained evidence boolean only when the Result is built.

## Start here

| File | Example |
| --- | --- |
| [`dispatch.rs`](dispatch.rs) | Dispatches `EqualFact`, `ForallFact`, `ExistFact`, and other fact shapes. |
| [`equality/core.rs`](equality/core.rs) | Handles `1 + 1 = 2` and algebraic equality routes. |
| [`well_definedness/fact.rs`](well_definedness/fact.rs) | Rejects `1 / 0 = 0` before proof search. |
| [`proof_search/builtin_rule.rs`](proof_search/builtin_rule.rs) | Applies bounded builtin verification rules. |
| [`proof_search/context_state.rs`](proof_search/context_state.rs) | Defines semantic initial, post-well-definedness, and final-round proof-search states. |
| [`proof_search/builtin_rule_state.rs`](proof_search/builtin_rule_state.rs) | Limits builtin-rule recursion independently from general proof search. |
| [`atomic/`](atomic) | Owns atomic lookup, definitions, strategies, and atomic-except-equality predicates. Universal candidate search and argument matching are separated under [`atomic/universal_search/`](atomic/universal_search). |
| [`quantified/`](quantified) | Owns universal, existential, and negated quantified facts. |
| [`builtin_rules/equality_dispatch/`](builtin_rules/equality_dispatch) | Dispatches equality-only set, tuple, order, and arithmetic rules by concept. |
| [`builtin_rules/number_compare/`](builtin_rules/number_compare) | Proves numeric order and sign facts through focused comparison families. |
| [`well_definedness/object/object.rs`](well_definedness/object/object.rs) | Dispatches recursive object well-definedness checks. |
