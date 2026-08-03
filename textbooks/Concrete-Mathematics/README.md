# Concrete Mathematics in Litex

This draft formalizes the non-exercise mathematical content of Chapters 1
through 3 of *Concrete Mathematics: A Foundation for Computer Science*. Chapter 1
studies recurrences through the Tower of Hanoi, planar regions, and the
Josephus problem. Chapter 2 develops finite sums, transformations of sums,
finite calculus, and the source's introduction to infinite sums. Chapter 3
implements integer functions from native floor/ceiling through the generalized
Josephus recurrence, real remainder, discrepancy, and the gcd floor-sum
reciprocity law, covering equations (3.1)--(3.32).

The canonical development entrypoint is:

```text
target/release/litex -compact -r scripts/textbooks_drafts/Concrete-Mathematics
```

The exported namespaces are `chap1`, `chap2`, and `chap3`, in source order.
The draft provides callable recurrence, finite-sum, summation-factor,
harmonic, binary/radix, interval-count, spectrum, real-mod, discrepancy, and
floor-progression interfaces. Concrete probes cover Hanoi and Josephus values,
region counts, quicksort, rounding, the 1000-slot roulette count, generalized
Josephus thresholds, real remainder, square-root floor sums, and arithmetic
floor sums.

Natural and positive-natural predecessor recurrences are checked directly
where their carrier facts replay reliably. Source-facing statements retain
localized trust only at recorded boundaries: refined rounded carriers and
canonical selections, finite-cardinality decompositions, calculus-level
almost-everywhere continuity/integration, compact discrepancy-maximum existence
and boundary corrections, advanced source closed forms, and a small set of cold-replay
performance fallbacks. Chapter 3 Section 3.1 is fully checked, including the
rounding gap, characterizations, reflections, integer shifts, and comparison
equivalences. In Section 3.2, both square-root commutation laws, both nested
positive-integer quotient laws, the general rounding-compatible-map theorem,
binary-digit length, all four interval-count formulas, and integer adjacency
are also checked. The spectrum sequence and its N-valued prefix-count formula
are checked as well. The roulette object is now the checked cardinality of its
source-defined finite winner set, and its final closed-form algebra is checked;
only the generic cube-block cardinality decomposition remains trusted. The
complementary `sqrt(2)` spectrum theorem is checked through the source's
reciprocal and floor/ceiling argument; only the foundational fact
`sqrt(2) notin Q` remains localized as proof debt.
In Section 3.3, the general natural-valued floor quotient, the integer
half-split identity, both positive half selectors, and their strict-decrease
laws are checked. The generalized Josephus denominator, positive threshold
recurrence, least qualifying index, and N+-valued survivor are checked as
well; the least-index construction uses a finite set-builder over a natural
closed range, not a Josephus-specific kernel rule. Remaining Section 3.3 trust
has also been eliminated: the Knuth `N -> N+` and merge `N+ -> N` objects are
checked recursive definitions using those typed smaller-index helpers. No
recurrence-specific builtin was added. Chapter 3's real-mod definition, sign
bounds, scaling law, both equal-partition sums, the floor-distribution identity,
finite discrepancy expressions, all three N-valued rounded
carriers in Section 3.5, gcd commutativity proof, and final floor-sum
reciprocity are ordinary checked Litex; none is implemented by an
object-specific kernel rule. The three finite-sum identities use generic
pointwise finite-sum congruence and integer-shift reindexing rules; their
source-facing theorem and carriers are unchanged. The rounded carriers are checked unique
selections from nonnegative floor/ceiling values. Equation (3.27)'s floor-square-root
prefix-sum closed form is also checked by induction: consecutive floor-square-root
values are equal or adjacent, and the increasing case occurs at the next square.
The exact attempts and accepted boundaries are
recorded in the paired experiment journal and `todo.md`. The complete Chapter
3 release `-compact -f` gate passed again on 2026-08-02 after restoring both
checked recurrences. A profiled cold run took about 1268 seconds: Knuth and
merge completed in about 9.5 and 14.9 seconds, while unrelated existing
statements later in the file took as long as 148 seconds. A quiet interval is
therefore not evidence that either recurrence failed to replay. The complete
registered Chapter 3 gate passed once more after checking all three Section
3.5 rounded N carriers; the profiled run took about 1424 seconds and reached
the final reciprocity theorem. After replacing the old real-mod scaling trust,
one further profiled gate reached the same final theorem in about 1415 seconds;
the scaling proof itself took about 21.9 seconds. No `run_all` was run for
either small cleanup batch. After checking equations (3.24)--(3.26), the final
profiled registered gate reached the final theorem in about 2753 seconds; the
grouped theorem itself took about 156 seconds. No `run_all` was run. The complete
profiled registered gate after checking equation (3.27) exited 0 through the
final reciprocity theorem in about 3036 seconds; the new induction theorem took
about 295 seconds. No `run_all` was run for this batch. The complete
registered Chapter 3 gate after replacing equation (3.13)'s opaque count and
whole-formula trust by a checked finite-cardinality object plus one exact
cube-block decomposition boundary exited 0 through the final reciprocity
theorem on 2026-08-03. Chapter 3 now has 14 trust markers; `run_all` was not run.
The subsequent equation (3.14) cleanup kept that count at 14 while replacing
the whole complementary-spectrum conclusion by the single irrationality fact;
all Beatty counting algebra now checks. The one final Chapter 3 file gate for
this batch exited 0 through `floor_progression_reciprocity_332` on 2026-08-03;
`run_all` was not run.
Equation (3.29) now defines one coherent maximum predicate and selects
`discrepancy_329` with `have fn ... by exist!`. Only existence of that maximum
is trusted; uniqueness, nonnegativity, every-point bounds, attainment, and the
empty-prefix value are checked. This reduces Chapter 3 from 14 to 11 trust
markers. Its single final file gate was started after all paired updates but
interrupted at the user's request before an exit code was available; it remains
the next continuation gate. No `run_all` was used for this small continuation.
The complete
registered three-chapter `-compact -r` gate
also passed after one implicit equality composition in Section 3.3 was written
as an explicit Litex calculation chain; that repair added no trust. The
release `run_all` test also passed with all 344 selected example and
documentation runs OK.
