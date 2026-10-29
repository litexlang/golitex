# Real restriction of the Jacobian counterexample

This example formalizes the real restriction of the three-variable polynomial
map recorded in [Gao, arXiv:2608.00222v1, Section 3.4](https://arxiv.org/html/2608.00222v1#S3.SS4).
[Speyer's July 20, 2026 account](https://sbseminar.wordpress.com/2026/07/20/the-new-counterexample-to-the-jacobian-conjecture/)
attributes the discovery to Fable and Levent Alpöge. The original source concerns
complex affine space. This example proves the real statement, using the existing
real analytic Jacobian interface; it does not formalize the complex theorem or a
polynomial-ring automorphism statement.

The Jacobian question asks whether a polynomial map on `C^n` with one fixed
nonzero Jacobian determinant must have a polynomial inverse. The cited source
answers no in dimension three. This file checks the real restriction: its
Jacobian determinant is always `-2`, but two distinct inputs have the same
image. This rules out every left inverse on `R^3`, including a polynomial one.

With `u=1+x*y`, the map has components

```text
P = u^3*z + y^2*u*(4+3*x*y)
Q = y + 3*x*u^2*z + 3*x*y^2*(4+3*x*y)
R = 2*x - 3*x^2*y - x^3*z
```

Follow the four numbered sections in `main.lit`:

1. **Define the map and matrix.** `F` gives the three polynomial components;
   `J_entry` lists the proposed derivative entries, and `J(p)` is their matrix.
2. **Identify the Jacobian.** One claim proves `has_jacobian_at(F,p,3,3,J(p))`
   at every real point. Its three local scalar functions abbreviate the expanded
   component formulas. A local equality-transfer lemma connects them to
   `F(q)(row)`. The nine partial calculations are grouped by row inside this claim.
3. **Compute the determinant.** One claim expands `det J(p)` along the first
   row and proves it is `-2`. A short following block instantiates the Jacobian
   certificate before selecting its value and transfers that determinant.
4. **Exhibit the collision.** The noninjectivity proof evaluates the two inputs
   locally and compares their first coordinates. The final left-inverse argument
   uses this noninjectivity, without repeating the evaluations.

Auxiliary differentiation functions and the equality-transfer theorem stay
inside the Jacobian proof. The exact image calculations stay inside the
collision proof. Each supporting calculation appears next to the step it serves.
The only syntactic placeholder is `1=1` inside finite enumeration: the current
grammar requires a nonempty body, while the nine enumerated goals are checked
from the partial facts already proved in that same claim.

The local names are `F` for the map, `J(p)` for its proposed derivative matrix,
and `$is_left_inverse(G)` for the left-inverse relation `G(F(p))=p`.
`J` is an ordinary function with contract
`fn(p cart_n(R,3)) matrix(R,3,3)`. The ordinary helper
`J_entry(p,row,col)` writes the entry formulas by row;
`J(p)(row,col)` is the corresponding matrix entry. No template is needed.
The row and column indices use `1...3`, the existing closed integer range
`closed_range(1,3)`, so the upper endpoint `3` is included.
The case checker proves that the three row equalities cover this integer range
from its binder membership. No preliminary row-enumeration statement is needed.

The input is one vector in `cart_n(R,3)`, the existing finite real-sequence
carrier of length three, with coordinates `p(1)`, `p(2)`, `p(3)`. All function
and point domains use this same carrier directly. No separate carrier-equality
proof is needed. The example proves all nine partial derivatives inside the
Jacobian claim and establishes the two main analytic facts

```litex
forall p cart_n(R,3):
    $has_jacobian_at(F,p,3,3,J(p))
    det(jacobian(F,p,3,3),3)=-2
```

The explicit real-to-complex matrix membership supplies the existing `det`
interface's carrier requirement. It does not change the real domain of the
Jacobian. Facts are checked in order: the candidate is established before the
selector is used; well-definedness does not compute an unproved derivative.

Two distinct rational inputs share the image `(-1/4,0,0)`:

```text
(0,0,-1/4), (1,-3/2,13/2)
```

The inputs differ in their first coordinates. The source derives noninjectivity
and then uses that result to prove that no function on real three-dimensional
space is a left inverse. All of these claims use the explicit
map rather than an assumed Jacobian matrix.

The proof has no standard-library imports. The source theorem
`partials_equal(n,a,b,point,axis,L)`, local to the Jacobian claim, connects the
explicitly differentiated polynomial with `F(q)(row)`: a supplied partial candidate and pointwise equality
on the same `cart_n(R,n)` domain imply the same candidate for the other function.
Its complete proof is `by fn_extension a=b`, followed by equality substitution
in `$has_partial_derivative_at`. The existing native
`jacobian_at_from_definition/5` then assembles the nine partials. This edit adds
no native Obj/Fact/BT/strategy, Rust changes, user axioms or `trust`.

Run from the repository root:

```bash
target/release/litex -strict -lang en -f examples/real_analysis/jacobian_counterexample/main.lit
```

Verification is recorded in `acceptance.json`: strict standalone execution
without imports. No full Cargo, Lean, textbook or release gate is implied.
Lean compilation of this example has not been attempted.
