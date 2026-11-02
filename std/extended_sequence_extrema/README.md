# Extended real sequence extrema

For any integer start, the input domain is exactly `{j Z:j>=start}` and the
codomain is `extended_reals::ExtendedReal`. The actual entire native fn_range
supplies the total `\extended_tail_supremum<start>(a)` and
`\extended_tail_infimum<start>(a)`. All finite and infinite terms are allowed.

This implements the author's correction to Tao Analysis I 6.3.1 and supplies
the extended-valued sequence extrema needed for 6.4.6. It preserves the existing
real_sequence_extrema names and their fixed real-valued parameter contracts.
See [the author's errata](https://teorth.github.io/tao-web/analysis-i.html).

```ini
[import std]
ExtendedSequences = extended_sequence_extrema
Extended = extended_reals
[alias]
xseq = ExtendedSequences::main
xreal = Extended::main
[export]
main = "./main.lit"
```

Public bounds, leastness/greatestness and strict approach theorems quantify over
all ExtendedReal bounds/comparison values and return indices on the original
tail. The general set-level strict-approach proofs are also reused by
real_sequence_extrema. No finite-value or boundedness condition is added.

`\real_tail_as_extended<start,a>` is an actual function on the complete
original real sequence domain, with exactly the same values. Its range is
proved equal to fn_range(a) using native preimages and set extensionality.
Use existing fn_set_member to expose its exact signature before extracting
preimages; this is a proved function construction rather than a type assumption.

This complete example has both genuinely nonreal infinity values and computes
its exact extrema from public bounds:

```litex
release obj def xreal::extended_real_sup

release obj def xreal::extended_real_negate

release obj def xreal::extended_set_supremum

release obj def xreal::extended_set_infimum

release thm xreal::positive_infinity_is_extended_real

release thm xreal::negative_infinity_is_extended_real

have fn endpoint_tail(n {j Z:j>=-4}) xreal::ExtendedReal by cases:
    case n=-4: xreal::real_positive_infinity
    case n!=-4: xreal::real_negative_infinity

endpoint_tail(-4)=xreal::real_positive_infinity

endpoint_tail(-3)=xreal::real_negative_infinity

release thm xseq::extended_tail_supremum_bounds_members(-4,endpoint_tail,-4)

$xreal::extended_real_le(xreal::real_positive_infinity,\xseq::extended_tail_supremum<-4>(endpoint_tail))

release thm xreal::positive_infinity_le_only_itself(\xseq::extended_tail_supremum<-4>(endpoint_tail))

\xseq::extended_tail_supremum<-4>(endpoint_tail)=xreal::real_positive_infinity

release thm xseq::extended_tail_infimum_bounds_members(-4,endpoint_tail,-3)

$xreal::extended_real_le(\xseq::extended_tail_infimum<-4>(endpoint_tail),xreal::real_negative_infinity)

release thm xreal::only_negative_infinity_le_negative_infinity(\xseq::extended_tail_infimum<-4>(endpoint_tail))

\xseq::extended_tail_infimum<-4>(endpoint_tail)=xreal::real_negative_infinity
```

The module has 22 source statements: 12 named theorems, two propositions, three
actual function templates, one supporting real-carrier proof and four existing
imported-function exposures. Full-domain imported contracts, actual real
embedding use, the complete README and false/domain controls are retained in
experiments/. No new axiom, trust, native rule or kernel/WD change is introduced.
