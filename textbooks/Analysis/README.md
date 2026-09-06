# Analysis I: current runnable module

This is the current release-verified Analysis I prefix. It exports the
project introduction, Chapters 1--10, Appendix A, and the verified Chapter 11
prefix through Section 11.4 in the original namespace order. Chapter 11
Sections 11.5--11.10 remain quarantined in the draft workspace until their
proof and runtime gates are repaired.

The runnable module currently covers introductory mathematical language,
natural numbers, set theory, integers, and rationals. Representative public
interfaces include the induction and recursion developments in `chap2`, set
operations and finite-set results in `chap3`, integer/rational arithmetic in
`chap4`, the construction of the real numbers in `chap5`, sequential limits
and limsup/liminf in `chap6`, series in `chap7`, and infinite/countable-set
interfaces in `chap8`, limits, continuity, compactness, and equivalent
sequences in `chap9`, differentiation in `chap10`, and the Riemann integral
laws through Section 11.4 in `chap11`. Appendix A contains the formal logic
and proof-language examples.

Verify the final registered chapter under its configured prefix with:

```text
target/release/litex -f textbooks/Analysis/chapter11-riemann-integral.lit
```

The Chapter 11 acceptance boundary is the registered prefix ending at line
12481 (Section 11.4). Its current native `-f` gate returns `exit=0` with
`error=null` in 468.78 seconds under the 500-second hard limit. The later
Chapter 11 sections remain in `scripts/Analysis/.draft` and are not exported
or showcased here. Chapter 11 itself contains no `axiom`; the four existing
axiom interfaces in Chapters 5 and 8 are unchanged and remain disclosed.
