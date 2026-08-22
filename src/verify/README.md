# Verifying facts

`1 + 1 = 2` succeeds by calculation, while this input fails before verification because `x` may be zero:

```litex
forall x R:
    x ^ 2 / x = x
```

```text
verify_fact(1 + 1 = 2)
  verify_well_defined(1 + 1 = 2)
  dispatch EqualFact
  try closed numeric evaluation
  record RationalNormalization evidence
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

## Start here

| File | Example |
| --- | --- |
| [`verify_dispatch.rs`](verify_dispatch.rs) | Dispatches `EqualFact`, `ForallFact`, `ExistFact`, and other fact shapes. |
| [`verify_equality.rs`](verify_equality.rs) | Handles `1 + 1 = 2` and algebraic equality routes. |
| [`verify_fact_well_defined.rs`](verify_fact_well_defined.rs) | Rejects `1 / 0 = 0` before proof search. |
| [`verify_builtin_rule.rs`](verify_builtin_rule.rs) | Applies bounded builtin verification rules. |
