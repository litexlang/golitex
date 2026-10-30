# Real quadratic equations

## Scope and sources

This module implements the real coefficient problem a*x^2+b*x+c=0, including
linear, constant and zero-polynomial cases. The source anchors are OpenStax
*Intermediate Algebra 2e*, [9.2 completing the square](https://openstax.org/books/intermediate-algebra-2e/pages/9-2-solve-quadratic-equations-by-completing-the-square)
and [9.3 the quadratic formula](https://openstax.org/books/intermediate-algebra-2e/pages/9-3-solve-quadratic-equations-using-the-quadratic-formula).
Vieta, its converse and the total coefficient classification are explicit
library supplements. The curriculum location is S02.2. Complex roots belong
to S07.5; a formal polynomial ring and degree conventions belong to U05.3.

## Mathematical objects and fixed contracts

- `quadratic_value(a,b,c,x)` is a real-valued function for all four real
  parameters, including a=0. It evaluates a polynomial of degree at most two.
- `quadratic_discriminant(a,b,c)` is the real value b^2-4*a*c for all real
  coefficients. Its sign is not part of its definition domain.
- `quadratic_solutions(a,b,c)` is the actual subset of R whose elements solve
  the equation. It is a set-valued function, including R for all-zero
  coefficients, rather than a predicate about a supplied set.
- `quadratic_root_minus` and `quadratic_root_plus` are formula values with
  numerator -b minus/plus the principal square root. Their definition requires
  a!=0 and a nonnegative discriminant. Division is associated as division by
  a, then 2; this is mathematically the usual denominator 2*a. Neither name
  means smaller/larger root. Negative a reverses their order.

No structure, certificate predicate, axiom, trust, native rule, alternate
cardinality or general polynomial representation is introduced. Empty solution
sets and the infinite zero-polynomial solution set retain their exact meanings.

## Forward dependency spine

Native real arithmetic and principal roots -> value/discriminant/solution set
and guarded formula values -> square identity and both root/square implications
-> substitution of both formula values and exhaustiveness -> exact solution
set. Negative discriminant uses nonnegativity of a real square. Linear and
constant cases are proved directly and do not call a quadratic-root value.

The exact formula set is the union of two singleton sets. This remains valid
when the two formula values coincide. The current Litex literal two-element
set requires its displayed elements to be distinct; it must not force a
positive-discriminant premise into the general nonnegative-discriminant result.

Vieta supplies sum, product and difference of the formula values. These give
factorization and the sign-dependent order. The converse starts from ordinary
sum/product equations and derives factorization and the entire solution set;
r=s remains allowed. Repeated roots use a singleton, while positive
discriminant supplies distinct witnesses and the exhaustive union. Completed
squares supply an attained minimum for positive a and maximum for negative a.

## Evidence and uses

The final strict checkpoint accepted five functions and 23 named theorems in
28 source statements, 65 independent imported statements, a nine-statement
README excerpt and 16 final-only controls after a fresh Session replays all
65 positives. Every theorem has a full-domain imported caller. Parameter cases,
attained product bounds and OpenStax examples 9.21, 9.27 and the real part of
9.24 were checked. The user subsequently requested a pause and removal of
this round's tests and temporary verification artifacts; those files and the
pinned executable were removed. These are historical checkpoint results. They establish the
listed real-equation contracts, not every exercise or a whole algebra course.

The parameter family (m-1)*x^2+2*x+1=0 exercises every branch: m=1 is linear,
m=2 is repeated, m<2 with m!=1 has two distinct real roots, and m>2 has none.
At m=0 the formula-minus value is the larger root. A fixed-sum product bound
is the intended elementary application of the attained quadratic maximum.

## Boundaries

Reject a=0 and negative discriminant in the guarded formula values, complex
coefficients in this real interface, two distinct roots at zero discriminant,
zero-polynomial finiteness and a sign-independent ordering of the formula
branches. Generic polynomial arithmetic, complex-root solving, ordered-root
selectors and floating-point numerical stability are not supplied by this
module. Quadratic inequalities and further applications remain separate work.
