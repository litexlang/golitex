# Finite scalar and unary function sums

Numeric prefix sums are total real-valued source constructions on actual finite
real families, including the empty prefix. Function prefix sums are ordinary
functions on a specified actual real domain, not a new builtin sum overload.
Candidate derivative and continuity facts are separate from that construction.

Finite induction proves point-derivative closure from all used candidates and a
real neighborhood. Continuity induction uses ordinary relative continuity and
requires no derivative. The numerical result is a checked R-valued prefix
function, so selector WD never guesses a sum or derivative. An explicit source
index-equality theorem transports successor indices such as0+1 to1 without
changing the equality checker. Existing finite_set_sum, fn, real arithmetic,
function extensionality and first-order BTs are reused. Two templates and eleven
source thms add no native AST, state, trust, strategy or theorem reservation.
