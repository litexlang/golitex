# Mathematics in Litex: current registered module

This registered module exports the introduction and Chapters 1--13. It
includes introductory functions and bounds, setting-based algebraic basics,
propositional logic, sets and functions, elementary number theory, and discrete
mathematics, together with the callable structure, Gaussian-integer, and
group-and-ring, linear-algebra, topology, differential-calculus, and
measure/integration construction slices. The single reader-facing `chap2`
export starts with named settings and retains the first-class structure values,
their laws, and the later-chapter interfaces in the same Chapter 2 file.
Where the former two surfaces had the same theorem name, the setting theorem
keeps that name and the bundled structure-facing theorem uses `_structure`.

Chapters 3 and 7 now expose the mathematics that their last eight direct
proof trusts previously hid (`1 -> 0` and `7 -> 0`). Chapter 3 checks the
Brahmagupta--Fibonacci product identity from the visible generic ring laws.
Chapter 7 checks permutation group laws by function and record extensionality,
all ten Gaussian commutative-ring laws coordinatewise, signed centered integer
division and its sharp remainder bound, and the Gaussian Euclidean norm
estimate before assembling the callable `EuclideanDomain<GaussInt>` object.
Both focused file gates pass on Litex 0.9.116-beta; the original source-facing
theorem and structure-object names remain callable.

Chapter 4's complete image/preimage set-map slice is now checked directly from
its visible callable constructions. Fourteen binary, mixed, and indexed-family
theorem-body trusts were replaced without changing their declarations or
adding imports. The later Schröder–Bernstein pass replaced the recursive
`sb_aux_successor` boundary, and the elementary real-function examples now use
native `ln`, `exp`, `sqrt`, and `x^2` objects directly instead of three opaque
function wrappers. Their injectivity and surjectivity proofs are checked, so
Chapter 4 now has `24 -> 0` direct trusts. The public `sb_aux`, `sb_set`,
`sb_fun`, and `schroeder_bernstein` interfaces are unchanged. The canonical
file passes on 2026-08-24.
Chapter 7's function-result projections continue to use checked typed result
helpers; the completed trust cleanup extends that explicit pattern through its
ring and Euclidean-domain law packages.
Chapter 6 now replaces all 56 former direct trusts with native finite
induction/counting, length-indexed list operations, and fully visible native-N
codes for trees and propositional formulas, including decreasing recursion and
derived structural induction. Chapter 8 replaces all 13 former direct trusts:
generic natural/integer scalar actions are transparent recursive functions,
the integer Module and componentwise product objects are checked, and fraction
quotient multiplication is selected by checked unique existence after explicit
representative independence. Chapters 6, 7, and 8 each pass their canonical
release file gate with zero direct trust.
Chapter 9 returned after its nested group rewrites and distinguished
polynomial-coefficient cases were made explicit with continuous equality
chains. Its 17 pre-existing direct trusts remain explicit proof debt
(`17 -> 17`); both the canonical file and complete source module pass.
Chapter 10 returned after the current release replayed its selected linear
inverse and all 234 source-order blocks without the historical child-environment
collision. One redundant raw definition equality was removed after a liveness
probe; its 13 pre-existing direct trusts remain explicit proof debt
(`13 -> 13`). The registered file and complete source module both pass.
Chapters 11--13 joined the canonical module on 2026-08-23 after reciprocal
metric laws, operator-bound constructors, and their prerequisite algebraic
law packages were normalized to independent definition-owned FactIds. Their
34 pre-existing direct trusts remain explicit mathematical/library debt
(`34 -> 34`); no trust was added. Registered canonical gates for Chapters
11--13 and the complete source module all pass on Litex 0.9.116-beta.

On the current 2026-08-26 verifier, the complete module gate replays the new
C6--C8 files and continues through Chapter 10, then stops at the unrelated
Chapter 11 declaration `choice_index(pair choice_pairs) = pair[1]` because the
well-definedness checker no longer recovers the tuple carrier of `pair`. The
exact current failure is recorded in the C6--C8 acceptance note; it is not a
remaining trust or proof hole in Chapters 6--8.

```text
target/release/litex -compact -runner -r scripts/mathematics_in_litex/textbook
```

The previous quarantine README is preserved only as historical context.
