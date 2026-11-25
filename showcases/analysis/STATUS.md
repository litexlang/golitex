# Coverage and assumptions

This public selection contains mathematical code from Chapters 2–8 of an
independent Litex adaptation of Terence Tao's *Analysis I*, plus Appendix A.
It follows chapter order; it does not claim complete coverage of the source
book, all exercises, or Chapters 9–11.

The separate [calculus companion](calculus/README.md) now demonstrates native
point derivatives, antiderivatives, Newton–Leibniz, nonmonotone substitution
and integration by parts. Its manifest and documented strict check cover that
module only. It adds no source trust or chapter assumptions and
does not certify a translation of Chapters 9–11. Native derivatives require
interior points; the book's relative-domain and endpoint derivatives have a
wider meaning.

## Included proof scope

The selected development includes natural-number induction, maps and finite
cardinality, rational and real-number interfaces, sequence limits, series
convergence tests, countable unions, Cantor's power-set argument and product
representations. The public sources include the following results:

- Chapter 5: `zero_positive_fractional_power`.
- Chapter 6: `positive_base_power_preserves_sequence_limit`.
- Chapter 7: finite scalar multiplication of sums, harmonic dyadic bounds,
  alternating tail pairs, shifted absolute-sum bounds, condensation bounds,
  bounded-prefix rearrangement estimates and bounded positive root terms.
- Chapter 8: `countable_union_of_at_most_countable_sets`.

## Omitted for space

The following branches are outside this selection. Their omission is not a
proof of the omitted statements.

| Omitted branch |
| --- |
| Finite integer shift variant |
| Ratio-limit-one implies root-limit-one extension/example |
| Set-indexed sums, cofinality, finite support, zero extension and operations |
| Conditional positive/negative subseries and Riemann rearrangement construction |
| Decimal proof of real uncountability |
| Finite total order, good-chain and advanced order/Zorn branch |

The independent Cantor power-set argument is included. Decimal-series proof
fragments are not presented as completed results. Chapters 9–11 and examples
with unclear intended statements or conditions are outside this showcase.

## Explicit assumptions that remain

The registered chapter sources retain four user axioms and one exported
abstract predicate signature:

| Source | Declaration | Role |
| --- | --- | --- |
| [Chapter 5](chapter05-real-numbers.lit) | `cauchy_sequence_representative_in_Q_exists` | Rational Cauchy representatives for real values |
| [Chapter 5](chapter05-real-numbers.lit) | `real_cauchy_sequence_has_limit_in_R` | Completeness of the builtin real carrier |
| [Chapter 8](chapter08-infinite-sets.lit) | `axiom_of_choice_for_index_cart` | Choice for indexed products |
| [Chapter 8](chapter08-infinite-sets.lit) | `axiom_of_choice_for_subsets` | Choice for families of subsets |
| [Chapter 8](chapter08-infinite-sets.lit) | `choice_property` (`abstract_prop`) | An abstract choice predicate; a signature is not itself a theorem |

Chapter 2 also declares `induction_demo` and `strong_induction_demo` inside
discarded `sketch` scopes. They are local predicate signatures for conditional
induction demonstrations, not exported facts.

These are retained background interfaces, not proved foundations. The full
chapter gate was **non-strict**. Zero active direct `trust` does not mean
assumption-free mathematics: the check also relies on Litex's builtin number
systems, operations, choice interfaces, inference rules and verifier.
No independent audit of those rules or kernel soundness proof is supplied here.

## Verification and publication boundary

[verification.json](verification.json) records the successful original
registered Chapter 8 run, the pinned executable hash and the ten original
source hashes. Publication removes inactive prose and comments, preserving
all executable lines and their order. The record separately identifies
executable-content equality, public parse checks and the small README example
check. Parsing alone is not proof verification. No Lean replay or whole-book
acceptance is claimed.

The earlier small-example receipt is retained as
[selected-examples-verification.json](selected-examples-verification.json).
Its strict result applies to that dated four-export selection, which includes
a separate public sequence-limit dependency; it does not certify the current
chapter exports.
