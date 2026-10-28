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

Follow the numbered comments in `main.lit` in mathematical order:

1. Define the polynomial map by its three component formulas.
2. Write the proposed derivative matrix, with a complete set of row cases.
3. Differentiate each coordinate in each input direction and connect the result to its matrix entry.
4. Assemble these nine proved partials into the actual Jacobian candidate.
5. Compute the three 2x2 minors and first-row terms, expand the determinant and cancel to -2; then transfer this value to the selected Jacobian.
6. Use exact `eval` on two distinct inputs to obtain equal images, proving noninjectivity.
7. A left inverse would turn equal images into equal inputs, contradicting the noninjectivity just proved.

Component calls such as `F(p)(1)` use the function definition directly; the
proof does not store a separate global list of its three coordinate equations.
The two concrete images are proved by `eval F(point)`, which checks the exact
computation and records its equality in each claim.
The comments immediately above each proof statement explain its contribution.
The only non-mathematical placeholder is `1=1` inside finite enumeration:
the current grammar requires a nonempty body, while the nine enumerated goals
are checked from the preceding partial claims. The source marks this explicitly.

The local names are `F` for the map, `\J<p>` for its proposed derivative matrix,
and `$is_left_inverse(G)` for the left-inverse relation `G(F(p))=p`.
The row and column indices use `1...3`, the existing closed integer range
`closed_range(1,3)`, so the upper endpoint `3` is included.

The input is one vector in `cart_n(R,3)`, the existing finite real-sequence
carrier of length three, with coordinates `p(1)`, `p(2)`, `p(3)`. All function
and point domains use this same carrier directly. No separate carrier-equality
proof is needed. The example proves all nine partial derivatives, assembles
the actual analytic Jacobian, and proves

```litex
forall p cart_n(R,3):
    $has_jacobian_at(F,p,3,3,\J<p>)
    jacobian(F,p,3,3) $in matrix(R,3,3)
    jacobian(F,p,3,3) $in matrix(C,3,3)
    jacobian(F,p,3,3)=\J<p>
    det(jacobian(F,p,3,3),3)=det(\J<p>,3)=-2
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

The proof imports `real_multivariable` and reuses
`locality::real_partials_extensional/8` and `jacobian_at_from_definition/5`.
It adds no native Obj/Fact/BT/strategy, Rust changes, user axioms or `trust`.

Run from the repository root:

```bash
target/release/litex -strict -lang en -f examples/real_analysis/jacobian_counterexample/main.lit
```

Verification is recorded in `acceptance.json`. It covers this source and the
canonical standard-library import; no full Cargo, Lean, textbook or release gate
is implied. Lean compilation of this example has not been attempted.
