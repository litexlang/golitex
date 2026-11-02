# Real exponent limits and source compatibility

This module covers Tao Analysis I 6.7.1-6.7.3. Positive bases, arbitrary finite
real exponents, actual rational approximants and complete original integer-tail
domains retain the existing native power operation and sequence interfaces.

For any real tail a tending to alpha and any fixed base>0, the actual positive
sequence base^a(n) tends to base^alpha. Specializing to rational exponent data
proves existence and independence of the source power limit. The existing
rational_floor_sequence supplies an actual approximant for every alpha in R.
Every candidate output limit equals the native power. Thus the source
limit-based definition characterizes the established operation, including its
rational-exponent values.

The remaining order laws now allow all real exponents: a positive real exponent
preserves and reflects strict order between positive bases; exponent order is
preserved for base>1 and reversed for 0<base<1, in both directions. Existing
real_power_laws already supplies real-domain positivity, addition, iteration,
reciprocal and the corrected product law, and is reused directly.

| Interface after ex:: | Mathematical role |
| --- | --- |
| \real_tail_function_image<start,a,f> | Actual image f(a(n)) for a complete real function. |
| continuous_real_image_preserves_tail_limit | Source epsilon limit transfer at a point of continuity. |
| \positive_base_real_power_function<base> | Actual complete R->R+ function t -> base^t. |
| positive_base_real_power_function_continuous | Continuity at every real exponent. |
| \real_tail_fixed_base_power<start,a,base> | Actual original-domain positive power sequence. |
| real_tail_fixed_base_power_limit | Real-input sequence limit transfer for every positive base. |
| real_tail_rational_power_limit | Rational inputs through their existing exact real view. |
| every_real_exponent_has_rational_power_approximants | Actual floor approximants and their powered limit. |
| rational_exponent_tail_power_limit_is_native | Uniqueness identifies every output limit with base^alpha. |
| rational_exponent_tail_power_limits_independent | Different rational approximants and integer starts give the same output limit. |

The example uses the actual rational floor approximants of sqrt(2), bases below,
at and above one, a guarded selected limit, negative exponents and the complete
real-domain order/algebra laws:

```ini
[import std]
Exponents = real_exponent_limits
Real = real_sequences
Power = real_power_laws
RationalLimits = rational_sequence_limits
Rational = rational_sequences
Approximation = real_approximation
[alias]
ex = Exponents::main
rs = Real::main
power = Power::main
rql = RationalLimits::main
rseq = Rational::main
approx = Approximation::main
[export]
main = "./main.lit"
```

```litex
release thm rseq::rational_floor_sequence_real_limit(sqrt(2))

release thm rql::rational_native_limit_is_genuine(1,\rseq::rational_floor_sequence<sqrt(2)>,sqrt(2))

release thm ex::real_tail_rational_power_limit(1,\rseq::rational_floor_sequence<sqrt(2)>,2,sqrt(2))

release thm ex::real_tail_rational_power_limit(1,\rseq::rational_floor_sequence<sqrt(2)>,1,sqrt(2))

release thm ex::real_tail_rational_power_limit(1,\rseq::rational_floor_sequence<sqrt(2)>,1/2,sqrt(2))

release thm rs::real_tail_limit_implies_convergent(1,\ex::real_tail_fixed_base_power<1,\rql::rational_tail_as_real<1,\rseq::rational_floor_sequence<sqrt(2)>>,2>,2^sqrt(2))

release thm rs::real_tail_limit_value(1,\ex::real_tail_fixed_base_power<1,\rql::rational_tail_as_real<1,\rseq::rational_floor_sequence<sqrt(2)>>,2>,2^sqrt(2))

\rs::real_tail_limit<1>(\ex::real_tail_fixed_base_power<1,\rql::rational_tail_as_real<1,\rseq::rational_floor_sequence<sqrt(2)>>,2>)=2^sqrt(2)

release thm ex::every_real_exponent_has_rational_power_approximants(2,-sqrt(2))

release thm ex::positive_real_exponent_power_preserves_strict_base_order(2,3,sqrt(2))

release thm ex::positive_real_exponent_power_reflects_strict_base_order(2,3,sqrt(2))

claim:
    ? -sqrt(2)<sqrt(2)
    sqrt(2) $in R+
    sqrt(2)>0
    -sqrt(2)<0
    -sqrt(2)<0<sqrt(2)

release thm ex::real_exponents_order_above_one(2,-sqrt(2),sqrt(2))

release thm ex::real_exponents_order_below_one(1/2,-sqrt(2),sqrt(2))

release thm ex::real_power_reflects_exponents_above_one(2,-sqrt(2),sqrt(2))

release thm ex::real_power_reflects_exponents_below_one(1/2,-sqrt(2),sqrt(2))

release thm power::positive_real_power_addition(2,sqrt(2),-sqrt(2))

release thm power::positive_real_power_iteration(2,sqrt(2),sqrt(2))

release thm power::positive_real_power_negative_exponent(2,sqrt(2))

release thm power::positive_real_product_power(2,3,sqrt(2))

release thm power::positive_real_power_is_positive(2,sqrt(2))
```

Publish convergence before using the partial real-tail limit selector. The
rational view and its exact original domain come from rational_sequence_limits;
all function data here has its stated carrier, including positive power
outputs and complete real-domain image functions.

Proof basis: existing native exp/ln identities and exponential continuity,
established power arithmetic, exact function composition and ordinary source
epsilon arguments. A delta/2 source cutoff handles strict native continuity
control and closed source sequence closeness. The fixed-base function is actual
data and is reused as that same function in its sequence image. Explicit 1<e
supplies the logarithm base-order premise in real-exponent order proofs.

The module has 18 source statements: three actual function templates and 15
named theorems. Full new and reused theorem domains, complete examples, distinct
lower/upper rational approximants, exact function values and negative controls
are checked in experiments/. General expression verification and evidence
composition/reuse remain shared verify responsibilities. No native source
change, build, new axiom or trust is part of this implementation. Native lim
keeps its one-argument real N+ sequence contract.
