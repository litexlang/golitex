# Real powers, nonnegative roots and rational exponent order

This module covers Tao, *Analysis I*, section 5.6, retaining native scalar `^`.
It derives positive-real power algebra from existing natural-log identities,
proves natural-power order by induction, and identifies each nonnegative
native nth root with the source supremum of its actual sublevel set.
No second power or real-number model is introduced.

```ini
[import std]
Powers = real_power_laws
[alias]
pwr = Powers::main
[export]
main = "./main.lit"
```

## Domains and interfaces

There are 44 named theorems and one construction template.

| Family | Exact domain and behavior |
| --- | --- |
| `positive_real_power_*` algebra and `positive_real_product_power` | Positive real bases, arbitrary real exponents. Addition, iteration, negative exponents and product powers hold. |
| `positive_real_nonzero_power_is_injective` | Positive real bases and a nonzero real exponent. Equal powers imply equal bases. |
| `nonnegative_real_natural_power_*` | Nonnegative real bases and natural exponents, including zero. Strict base order requires a positive natural exponent. |
| `nonnegative_real_root_*` | Nonnegative real input and positive natural root index. Roots are real and nonnegative, satisfy the power equation, and are uniquely characterized among nonnegative candidates. |
| `\nonnegative_root_sublevel_set<x,n>` | x belongs to `{t R:t>=0}`, n belongs to N+. The actual real subset `{y R:y>=0 and y^n<=x}`. |
| `real_roots_decrease_with_index_above_one` | x>1 and positive integer indices m<n imply root_n(x)<root_m(x). |
| `real_roots_increase_with_index_below_one` | 0<x<1 and m<n imply root_m(x)<root_n(x). |
| `positive_real_rational_power_*` order | Positive real bases and positive rational exponent. Strict base order holds in both directions. |
| `real_rational_exponents_order_*` and reflection counterparts | Rational exponents of either sign. Base>1 preserves their strict order; a positive base<1 reverses it. |

All names above follow `pwr::` in a caller. No public operation is selected by
argument count or scalar/vector type. Existing natural and integer powers keep
their native domains, including `0^0=1` and negative bases at integer exponents.
The root construction and root characterizations require nonnegative input;
this module introduces no convention for negative-real noninteger roots.

## Algebra and source root definition

`natural_log_is_injective`, `natural_log_of_real_power` and
`natural_log_of_positive_product` are checked source proof dependencies. They
use the existing native logarithm identities with explicit positive nonunit
base evidence for e. The power-algebra theorems preserve native power values;
they do not assume the desired rational/real power laws or add a native rule.

For a nonnegative input, the root real-carrier theorem makes the actual value
available before products and compositions. `nonnegative_real_root_properties`
gives nonnegativity and root_n(x)^n=x.
`nonnegative_real_root_unique` proves the converse for every nonnegative
candidate. `positive_real_root_is_positive` and
`nonnegative_real_root_reflects_positivity` give positivity exactly when x>0.
Thus zero has root zero, as required by the author's correction to 5.6.6(c).

The sublevel-set membership theorems expose both its nonnegative condition
and power bound. Its root is an actual member and upper bound, hence a maximum.
The set is nonempty and bounded, the root is its native least upper bound,
and `nonnegative_real_root_equals_supremum` identifies the actual finite
supremum with x^(1/n). Establish `nonnegative_root_sublevel_has_real_supremum`
before writing that native partial selector in a new context.

Root product and composition laws include zero. Root-index strict monotonicity
retains the corrected 0<x<1 condition and positive integer indices; zero and
one have constant root values. The fractional-power formula allows every
integer numerator and positive integer denominator. Equal fraction
representations give equal root-power formulas. Reduced fractions and the
proved natural-power order give rational-power order without an extra
positivity or boundedness assumption.

## Complete example

This caller verifies the source supremum at zero, a fourth-root value and
composition, and the equality of two fractional exponent representations:

```litex
release thm pwr::nonnegative_root_sublevel_has_real_supremum(0,2)
release thm pwr::nonnegative_real_root_equals_supremum(0,2)
sup(\pwr::nonnegative_root_sublevel_set<0,2>) = 0^(1/2) = 0
release thm pwr::nonnegative_real_root_unique(16,2,4)
16^(1/4) = 2
release thm pwr::nonnegative_real_root_composition(16,2,2)
(16^(1/2))^(1/2) = 16^(1/(2*2)) = 16^(1/4) = 2
release thm pwr::positive_real_rational_power_fraction_independent(2,1,2,2,4)
(2^(1/2))^1 = (2^(1/4))^2
release thm pwr::positive_real_power_negative_exponent(2,-3/2)
2^(-(-3/2)) = 1/(2^(-3/2))
```

The source's added 5.6.9(f) product law is supplied by
`positive_real_product_power`, with real exponents as well as rational ones.
General real-exponent order is outside this increment's order API; rational
order is proved at the full source domain. Source correspondence, corrected
zero/one boundaries, full imported contracts and strict verification receipts
remain in the owning experiments workspace. No kernel, WD, parser, compiler,
new axiom or source trust change is used.
