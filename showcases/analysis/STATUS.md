# Coverage and assumptions

This public selection contains mathematical code from Chapters 2–8 of an
independent Litex adaptation of Terence Tao's *Analysis I*, plus Appendix A.
It follows chapter order; it does not claim complete coverage of the source
book, all exercises, or Chapters 9–11.

The separate [calculus companion](calculus/README.md) now demonstrates native
point derivatives, antiderivatives, Newton–Leibniz, nonmonotone substitution
and integration by parts. Its own manifest and strict
[2026-10-24 receipt](../verification_runs/2026-10-24-native-calculus.json)
cover that module only. It adds no source trust or chapter assumptions and
does not certify a translation of Chapters 9–11. Native derivatives require
interior points; the book's relative-domain and endpoint derivatives have a
wider meaning.

## Included proof scope

The selected development includes natural-number induction, maps and finite
cardinality, rational and real-number interfaces, sequence limits, series
convergence tests, countable unions, Cantor's power-set argument and product
representations. The ten selected mainline targets were completed in the
original verified inputs. Two comment-only introduction exports have since
been removed, leaving eight executable mainline targets. The public copies preserve all their executable
code, including the following results:

- Chapter 5: `zero_positive_fractional_power`.
- Chapter 6: `positive_base_power_preserves_sequence_limit`.
- Chapter 7: finite scalar multiplication of sums, harmonic dyadic bounds,
  alternating tail pairs, shifted absolute-sum bounds, condensation bounds,
  bounded-prefix rearrangement estimates and bounded positive root terms.
- Chapter 8: `countable_union_of_at_most_countable_sets`.

## Omitted for space

Eighteen earlier direct-trust sites belonged to branches deliberately removed
from the selection. Of 65 earlier sites, 47 were replaced by proofs and 18
removed with these branches, leaving zero active direct trusts. Their removal
is scope reduction, not proof completion:

| Omitted branch | Earlier direct-trust sites |
| --- | ---: |
| Finite integer shift variant | 1 |
| Ratio-limit-one implies root-limit-one extension/example | 1 |
| Set-indexed sums, cofinality, finite support, zero extension and operations | 9 |
| Conditional positive/negative subseries and Riemann rearrangement construction | 2 |
| Decimal proof of real uncountability | 1 |
| Finite total order, good-chain and advanced order/Zorn branch | 4 |

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

The [2026-10-14 repair receipt](../verification_runs/2026-10-14-showcase-repair.md)
records fresh ordinary acceptance of all eleven current exports, plus a strict
check of the three small examples with their explicit map dependency. The
finite-product proof now supplies explicit carrier and predicate projections;
its two original theorem goal blocks remain unchanged.
