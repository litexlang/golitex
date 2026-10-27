# Higher real derivative source interfaces

This file inventories the two higher-order exports; the existing coordinate,
directional, cross-product and integral exports are described in README.md.

| Export | Objects and propositions | Checked source results |
| --- | --- | --- |
| locality | Real punctured-neighborhood and actual coordinate-domain comparison | 15 source theorems and a reverse-induction invariant: common-neighborhood uniqueness, difference quotients and candidate transport |
| higher_order | OrderedPartialProfiles; profile function; chain/candidate/existence and induction invariant; ordered_partial<n,D,k>(f,p,indices) | 25 theorems: arbitrary finite-order uniqueness/selection, zero order, native first/second bridges, supplied full-space profiles explicit candidate-valued prefix restriction, exact-domain derivative functions and successor coherence |
| unary_higher_order | NthDerivativeProfiles; real profile function; chain/candidate/existence and induction invariant; nth_derivative<D,k>(f,p) | 23 theorems: arbitrary finite-order uniqueness/selection, zero order, native first bridges and supplied full-real profiles explicit candidate-valued lower restriction, exact-domain derivative functions and successor coherence |

All regions are actual domains. The final region contains the requested point;
each preceding native derivative consumes its two-sided neighborhood obligation.
Scalar and vector-input interfaces have distinct names and parameter contracts.
No new native AST, BT, strategy, runtime state, axiom or trust is introduced.

Higher-order linearity, mixed-partial exchange, C^k and alpha-count interfaces
are not provided by these exports. No dedicated LaTeX formatter or Lean replay
coverage is claimed for their ordinary source selectors in this increment.

The derivative function construction separates the source domain D from an
actual derivative domain E⊆D. Its all-point existence prop is checked first;
`ordered_partial_function<n,D,E,k>(f,indices)` returns `fn(p E) R`, while the
independent unary `nth_derivative_function<D,E,k>(f)` returns `fn(p E) R`.
No extra pointwise guard shrinks E. Candidate-valued restriction of a supplied
certificate identifies its intermediate profile with that selected function.
Successor coherence transports the next native candidate on the same actual E.
Neither existence alone nor this transport specifies arbitrary numeric values.

The locality export now proves restriction to a smaller actual domain under an
explicit two-sided/coordinate neighborhood condition there. Its former equal-domain
transport interfaces keep their contract and reuse these general restriction
proofs. A plain subset containing the point is insufficient.
