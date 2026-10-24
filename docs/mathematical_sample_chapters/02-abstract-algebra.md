# Homomorphisms and lost information

The functions $d(n)=2n$ and $z(n)=0$ both preserve integer addition:
$f(m+n)=f(m)+f(n)$. Yet they preserve very different amounts of information.
Knowing $d(n)$ determines $n$, whereas knowing $z(n)$ tells us nothing about
which integer was supplied.

We will locate that difference in a subset called the kernel. The central
theorem works for all groups, including noncommutative ones: a group
homomorphism is injective if and only if its kernel contains only the identity.
Integer doubling and the zero map will make both outcomes concrete.

## An operation and its laws

A group consists of a nonempty set, an associative operation, an identity and
inverses. In multiplicative notation, its laws include

$$ (ab)c=a(bc),\qquad 1a=a1=a,\qquad a^{-1}a=aa^{-1}=1.$$

Commutativity is not required. Integer addition is one group example: its
identity is $0$, its inverse operation is negation, and its multiplication
notation means addition. The beginning of the
[complete lecture](../../showcases/abstract_algebra/abstract_algebra.lit)
provides this standalone calculation.

```litex
have fn integer_add(x, y Z) Z = x + y

have fn integer_neg(x Z) Z = -x

integer_add(3, -3) = 0

integer_add(integer_add(2, 3), 4) = integer_add(2, integer_add(3, 4))
```

The lecture packages the operations and checked laws into `Group<A>`, then
constructs `integers` as an instance. Its fields are named `mul`, `one` and
`inv`. Thus `integers.one` equals zero. These names allow the same theorem to
apply to additive and multiplicative examples without changing its meaning.

## Why cancellation is available

From $ab=ac$, multiply on the left by $a^{-1}$ and use associativity:

$$b=1b=(a^{-1}a)b=a^{-1}(ab)=a^{-1}(ac)=(a^{-1}a)c=c.$$

Every equality has a reason, and no factor changes order. Cancellation is a
consequence of the group laws. It need not be added as a further assumption.
Similarly, if $ba=1$, then
$b=b(aa^{-1})=(ba)a^{-1}=a^{-1}$, so a left inverse is the designated inverse.

These two facts explain why homomorphisms preserve more than their definition
explicitly asks for. The lecture defines a homomorphism by one law, in the
following excerpt with its existing group interface.

<!-- litex-source: ../../showcases/abstract_algebra/abstract_algebra.lit -->
<!-- litex:skip-test -->
```litex
prop is_homomorphism(A nonempty_set, G &Group<A>, B nonempty_set, H &Group<B>, f fn(x A) B):
    forall x, y A:
        f(G.mul(x, y)) = H.mul(f(x), f(y))
```

Put $u=f(1)$. Preservation of multiplication gives $u=u^2$, and cancellation
in the target group gives $u=1$. Next,
$f(a^{-1})f(a)=f(a^{-1}a)=f(1)=1$; uniqueness of inverses gives
$f(a^{-1})=f(a)^{-1}$. Identity and inverse preservation have been proved,
rather than silently included as extra requirements.

## The kernel measures a collision

The **kernel** is $\ker f=\{a\in A:f(a)=1_B\}$. It contains the domain
identity, and it is closed under the domain operation and inverse. Indeed,
if $f(x)=f(y)=1_B$, then $f(xy)=1_B$; if $f(x)=1_B$, then
$f(x^{-1})=f(x)^{-1}=1_B$. It is therefore a subgroup.

It is also normal. For $s\in\ker f$ and arbitrary $a$,
$f(asa^{-1})=f(a)1_Bf(a)^{-1}=1_B$. This does not require the source
group to be abelian. The lecture's `kernel_is_normal` proves these closure
facts using the same kernel set later consumed by the injectivity theorem.

Now suppose $f(x)=f(y)$. The element $y^{-1}x$ measures the collision:

$$f(y^{-1}x)=f(y)^{-1}f(x)=f(y)^{-1}f(y)=1_B.$$

If the kernel is trivial, then $y^{-1}x=1_A=y^{-1}y$. Cancellation gives
$x=y$. Thus a trivial kernel implies injectivity. Conversely, if $f$ is
injective and $f(x)=1_B=f(1_A)$, then $x=1_A$. This proves both directions.

The forward theorem states its two hypotheses separately. The excerpt below
is its exact statement in the complete source; its proof uses inverse
preservation followed by cancellation as above.

<!-- litex-source: ../../showcases/abstract_algebra/abstract_algebra.lit -->
<!-- litex:skip-test -->
```litex
thm trivial_kernel_implies_injective:
    ? forall A nonempty_set, G &Group<A>, B nonempty_set, H &Group<B>, f fn(x A) B:
        $is_homomorphism(A, G, B, H, f)
        $has_trivial_kernel(A, G, B, H, f)
        =>:
            $injective(A, B, f)
```

For an arbitrary function, the fiber above one selected value cannot describe
all its collisions. The group law is what lets us turn a collision anywhere
into an element of the kernel.

## Returning to the integers

For doubling, $d(m+n)=2m+2n=d(m)+d(n)$. Its kernel consists of solutions
to $2n=0$, hence only $0$. The theorem proves doubling is injective. It does
not prove doubling is surjective onto the integers: odd integers remain
outside its image.

The zero map also preserves addition, but every integer lies in its kernel.
In particular $z(0)=z(1)$, although $0\ne1$. The lecture checks both kernel
equalities and both injectivity outcomes.

Translation $s(n)=n+1$ provides a different test. It is injective, but it is
not an additive homomorphism: it sends the identity $0$ to $1$.
Injectivity alone says nothing about preserving an operation.

## Exercises

1. Determine the kernel and image of $f(n)=3n$ on the additive integer group.
2. Why is the set of nonnegative integers not a subgroup of the integers?
3. Show that the intersection of two subgroups of a fixed group is a subgroup.

## Answers

1. Its kernel is $\{0\}$ and its image is $3\mathbb Z$. It is injective but
   not surjective onto $\mathbb Z$, since $1$ has no integer preimage.
2. It contains the identity and is closed under addition, but the inverse of
   its element $1$ is $-1$, which is absent.
3. Both subgroups contain the identity. Two elements of their intersection
   have their product in each subgroup, hence in the intersection. The same
   argument applies to inverses.

## Continue reading

The [lecture map](../../showcases/abstract_algebra/README.md) connects subgroup
examples, normal kernels and the two directions of the criterion. This chapter
does not construct quotient groups or prove the isomorphism or Sylow theorems.
Those require additional developments beyond the kernel argument proved here.

[Previous](01-linear-algebra.md) · [Contents](README.md) · [Next: topology](03-topology.md)

