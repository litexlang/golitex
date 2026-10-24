# Vectors and unique coordinates

A vector such as `(3, 4)` already seems to come with coordinates. Why, then,
does linear algebra spend time defining a basis? Because coordinates describe
a vector relative to a chosen list of directions. We need to know that those
directions can reach every vector, and that they do not give competing
descriptions of the same vector.

We will answer both questions in the real plane. The result is concrete enough
to calculate by hand, but its two parts explain the general definition of a
basis: spanning supplies existence, and linear independence supplies uniqueness.

## Directions and operations

A plane vector is an ordered pair of real numbers. Addition and scalar
multiplication act coordinate by coordinate:

$$
(u_1,u_2)+(v_1,v_2)=(u_1+v_1,u_2+v_2),\qquad
a(v_1,v_2)=(av_1,av_2).
$$

Here is a standalone example, taken from the opening of the
[complete lecture](../../showcases/linear_algebra/linear_algebra.lit).
`R × R` is the real plane; `u(1)` and `u(2)` are the coordinates of `u`.

```litex
have fn plane_add(u, v R × R) R × R = (u(1) + v(1), u(2) + v(2))

have fn plane_smul(a R, v R × R) R × R = (a * v(1), a * v(2))

(1 + 3, 2 + 4) = (4, 6)

(3 * 1, 3 * 2) = (3, 6)

(3 * 1 + 4 * 0, 3 * 0 + 4 * 1) = (3, 4)
```

The final equality suggests two directions, $e_1=(1,0)$ and $e_2=(0,1)$.
The vector $(3,4)$ is $3e_1+4e_2$. For an arbitrary pair $(a,b)$, the same
calculation gives

$$ae_1+be_2=(a,0)+(0,b)=(a,b).$$

The lecture first checks the real field and vector-space laws. Its inverse
operation accepts only nonzero scalars; the coordinate operations above then
form the real-plane instance. This lets later definitions work with a field
and vector space, while the plane remains a concrete instance of them.

## Reaching every vector

A linear combination of a finite list $v_1,\ldots,v_n$ has the form
$a_1v_1+\cdots+a_nv_n$. Its coefficients may be zero. Its **span** is the set
of vectors obtainable in this way. A list spans the plane if every plane
vector belongs to that set.

For the two standard directions, the coefficients of $v=(v_1,v_2)$ are
immediately available: choose $v_1$ and $v_2$. The displayed identity proves
that their combination equals $v$. This proves spanning for every plane
vector, not just the numerical example $(3,4)$.

The lecture represents finite combinations by partial sums, including the
empty sum. In that context its span is an ordinary set defined by the
linear-combination relation. This is a source excerpt; the field, space and
relation have already been defined in the complete file.

<!-- litex-source: ../../showcases/linear_algebra/linear_algebra.lit -->
<!-- litex:skip-test -->
```litex
template<K nonempty_set, field &Field<K>, V nonempty_set, space &VectorSpace<K, field, V>, n N, vectors finite_seq(V, n)>:
    have span power_set(V) = {x V: $is_linear_combination(K, field, V, space, n, x, vectors)}
```

There is a distinction between an element of the span and a coefficient
list that produces it. The relation records the connection; the set collects
the resulting vectors. A later theorem may use either piece of information.

## Removing ambiguity

Spanning alone does not guarantee unique coefficients. For example, the list
$(e_1,e_1,e_2)$ spans the plane, but

$$3e_1+0e_1+4e_2=0e_1+3e_1+4e_2.$$

The problem is the nonzero coefficient relation $e_1-e_1=0$. A list is
**linearly independent** when every combination equal to zero has all its
coefficients zero. This excludes precisely the redundancy used above.

For $(e_1,e_2)$, a zero combination is $(a,b)=(0,0)$, so $a=b=0$.
Thus the standard directions are independent as well as spanning: they form
a basis. The general reason independence gives uniqueness is subtraction.
If two coefficient lists describe the same vector, subtract their expansions.
The differences of the coefficients give a zero combination, and independence
forces each difference to vanish.

In the plane, we can see the same conclusion directly. If
$v=ae_1+be_2=(a,b)$, equality of ordered pairs gives $a=v_1$ and $b=v_2$.
The lecture's theorem states exactly this implication. The excerpt uses its
previously constructed `standard_basis` and coordinate operations.

<!-- litex-source: ../../showcases/linear_algebra/linear_algebra.lit -->
<!-- litex:skip-test -->
```litex
thm standard_coordinates_unique:
    ? forall v R × R, a, b R:
        v = plane_add(plane_smul(a, standard_basis(1)), plane_smul(b, standard_basis(2)))
        =>:
            a = v(1)
            b = v(2)
```

The theorem header states what must be proved; its complete checked proof
follows in the linked source. No coefficient is chosen by declaring this
theorem. The earlier expansion supplies a representation, and the uniqueness
theorem constrains every proposed representation.

## Changing the directions

Consider $u=(1,1)$ and $w=(1,-1)$. Solving
$\alpha u+\beta w=(x,y)$ gives two equations:
$\alpha+\beta=x$ and $\alpha-\beta=y$. Adding and subtracting them gives

$$\alpha=\frac{x+y}{2},\qquad \beta=\frac{x-y}{2}.$$

Substitution proves existence, and the same two equations force uniqueness.
The vector is still $(x,y)$, but its coordinates relative to $(u,w)$ are now
$((x+y)/2,(x-y)/2)$. A basis changes the description, not the underlying vector.
This calculation is a worked mathematical extension; it is not a claim that
the lecture has formalized every change-of-basis theorem.

## Exercises

1. Express $(5,-1)$ in the basis $((1,1),(1,-1))$.
2. Show that $((1,0),(2,0))$ is dependent and does not span the plane.
3. Explain why a spanning list can fail to be a basis even if none of its
   entries is zero.

## Answers

1. The coefficients are $2$ and $3$: $2(1,1)+3(1,-1)=(5,-1)$.
2. The nonzero relation $2(1,0)-(2,0)=0$ proves dependence. Every combination
   has second coordinate zero, so $(0,1)$ is outside the span.
3. The list $(e_1,e_1,e_2)$ has no zero entry and spans the plane, but the
   repeated direction gives a nonzero zero combination.

## Continue reading

The [lecture and reading map](../../showcases/linear_algebra/README.md) continue
with arbitrary finite combinations, linear maps, kernels, ranges and a concrete
projection. This sample establishes unique coordinates for the standard basis
of the real plane. A general dimension theory requires further theorems about
arbitrary finite bases; it does not follow merely by counting these two vectors.

[Contents](README.md) · [Next: homomorphisms and kernels](02-abstract-algebra.md)

