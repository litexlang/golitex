# Mathematical interfaces

`base::k`, the current `k`, and `Values::base::k` are independent real objects
defined as 0, 1, and 2 respectively. Equal terminal names do not identify
objects from different exports. Correct defining equalities must verify;
`base::k = 1` must fail without an independent proof.

The three `shift` functions are real functions with formulas `x`, `x + 1`, and
`x + 2`. Their exported definitions and signature facts are consumed by
`release obj def`. The caller checks applications with different results and
builds a tuple containing two qualified objects. Undeclared export members
have no object interface and must fail well-definedness.
