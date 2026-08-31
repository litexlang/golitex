# Mathematics in Litex: current runnable module

This release-verified subset exports the introduction and Chapters 1--10. It
includes introductory functions and bounds, setting-based algebraic basics,
propositional logic, sets and functions, elementary number theory, and discrete
mathematics, together with the callable structure, Gaussian-integer, and
group-and-ring construction slices. The single reader-facing `chap2` export
starts with named settings and retains the first-class structure values, their
laws, and later-chapter interfaces in the same Chapter 2 file.

Chapter 4 returned to the runnable module after the kernel learned to reuse an
identical template object committed from a theorem child environment. Its
set-valued `inverse_fiber` interface and all pre-existing explicit proof debt
are unchanged; the canonical file and complete source module both pass.
Chapter 7 returned to the runnable module after its function-result projections
were routed through checked typed result helpers without changing the original
public theorem statements.
Chapter 8 returned after the inherited-submonoid multiplication was given a
declaration-owned function carrier and an exact checked Monoid bridge. Its 13
pre-existing direct trusts remain explicit proof debt (`13 -> 13`); both the
canonical file and complete source module pass.
Chapter 9 returned after its nested group rewrites and distinguished
polynomial-coefficient cases were made explicit with continuous equality
chains. Its 17 pre-existing direct trusts remain explicit proof debt
(`17 -> 17`); both the canonical file and complete source module pass.
Chapter 10 returned after the current release replayed its selected linear
inverse and all 234 source-order blocks without the historical child-environment
collision. One redundant raw definition equality was removed after a liveness
probe; its 13 pre-existing direct trusts remain explicit proof debt
(`13 -> 13`). The registered file and complete source module both pass.
Chapters 11--12 remain quarantined.
Chapter 13 passes only when the quarantined Chapter 12 namespace is trusted,
so it is also preserved under `../todo_textbook_chapters/` rather than
published as a coherent chapter.

```text
target/release/litex -compact -graph -r scripts/mathematics_in_litex/textbook
```

The previous full-corpus README is preserved with the quarantined chapters.
