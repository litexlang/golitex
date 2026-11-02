# Standard real sequence limits

All three actual data families have the complete original domain
`{j Z:j>=1}`. The reciprocal-root degree is a positive integer, the geometric
base is any real, and the fixed nth-root base is a positive real.

- `\reciprocal_natural_root_tail<degree>(n)` equals 1/(n^(1/degree)) and has
  real values. Its limit is zero for every degree in N+.
- `\real_geometric_tail_from_one<base>(n)` evaluates the native N+ geometric
  function at the proved positive original index. This preserves base^n for
  zero, negative and positive bases. The limit is zero for |base|<1 and one
  for base=1; base=-1 and |base|>1 have no finite real convergence.
- `\positive_base_nth_root_tail<value>(n)` has codomain R+ and equals
  value^(1/n). Its limit is one for every fixed value in R+, including bases
  below, at and above one.

The source predicates and guarded selected limit are the existing
[real_sequences](../real_sequences/README.md) interfaces. Native lim keeps its
one-argument N+ real-sequence contract. The domain guards belong to the data
families themselves.

This complete example checks all source cases and selects a fixed-root limit
after explicitly publishing convergence:

```ini
[import std]
Standard = real_standard_limits
Series = real_series
Power = real_power_laws
Real = real_sequences
Limits = real_sequence_limsup
Approximation = real_approximation
[alias]
sl = Standard::main
series = Series::main
power = Power::main
rs = Real::main
rsl = Limits::main
approx = Approximation::main
[export]
main = "./main.lit"
```

```litex
release thm sl::reciprocal_natural_root_tail_limit(1)

release thm sl::reciprocal_natural_root_tail_limit(2)

release thm sl::reciprocal_natural_root_tail_limit(5)

release thm sl::real_geometric_tail_small_base_limit(-1/2)

release thm sl::real_geometric_tail_small_base_limit(0)

release thm sl::real_geometric_tail_small_base_limit(1/2)

release thm sl::real_geometric_tail_one_limit

release thm sl::real_geometric_tail_minus_one_diverges

release thm sl::real_geometric_tail_large_magnitude_diverges(2)

release thm sl::real_geometric_tail_large_magnitude_diverges(-2)

release thm sl::positive_base_nth_root_tail_limit(1/2)

release thm sl::positive_base_nth_root_tail_limit(1)

release thm sl::positive_base_nth_root_tail_limit(2)

release thm rs::real_tail_limit_implies_convergent(1,\sl::positive_base_nth_root_tail<2>,1)

release thm rs::real_tail_limit_value(1,\sl::positive_base_nth_root_tail<2>,1)

\rs::real_tail_limit<1>(\sl::positive_base_nth_root_tail<2>)=1

release thm sl::real_geometric_tail_from_one_values(0,1)

\sl::real_geometric_tail_from_one<0>(1)=0

release thm sl::positive_base_nth_root_tail_power(1/2,1)

\sl::positive_base_nth_root_tail<1/2>(1)=1/2
```

Use `real_geometric_tail_from_one_values(base,k)` before imported point
calculations; k in N+ is proved to belong to the original domain. The fixed-root
power theorem gives root(n)^n=value, and its n=1 specialization exposes the
first value. The reciprocal-root value theorem gives positivity and
root(n)^degree=1/n. Existing root uniqueness laws compute exact higher-degree
values.

The proof of geometric decay reuses the full real_series geometric theorem on
an actual native N+ function and transports the exact original reindex values.
The minus-one proof contradicts source Cauchy steadiness at adjacent indices;
large absolute bases contradict boundedness through existing Bernoulli growth.

For reciprocal roots, an Archimedean cutoff for 1/epsilon^degree and strict
natural-power order give the source epsilon proof. Fixed roots above one use
Bernoulli growth and root-power order. Below one, the reciprocal-base root
limit and the exact scalar product identity give the same epsilon bound.
All source radii remain positive reals and closeness uses <=epsilon.

The module has 29 source statements: 12 named theorems, three actual function
templates and 14 supporting carrier/formation proofs. Its basis is existing
native real arithmetic and checked std power, sequence and Bernoulli laws.
No new axiom, trust, native rule or kernel/WD change is introduced. Complete
imported contracts, exact and irrational data examples, original-domain and
false-case controls, and strict receipts remain under experiments/.
