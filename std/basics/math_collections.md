# Mathematical design of `std/basics`

`std/basics` contains small source-level interfaces that are reused across
otherwise independent developments. It should not wrap concepts that already
belong to the Litex kernel. The declarations below are the main mathematical
nodes that determine the module's current shape.

## Finite subsets

Mathematically, every subset of a finite set is finite. This fact is needed to
construct bounded sets such as the positive common divisors of two integers.
Its current Litex form is a named standard-library axiom:

<!-- litex:skip-test -->
```litex
axiom subset_of_finite_set_is_finite:
    ? forall A set, B finite_set:
        A $subset B
        =>:
            $is_finite_set(A)
```

The nearest rejected form is a hidden builtin verifier rule. Keeping the fact
as an axiom makes its trust boundary and theorem dependency visible. It depends
only on builtin set membership, subset, and finite-set predicates. Its source
proof remains open; downstream users include the finite common-divisor set used
to define `gcd`.

## Zero-based indexing of finite sets

A finite set `s` of size `n` admits an enumeration by a bijection from
`range(0, n)`. The public interface is existential because clients need an
indexing function, not the induction machinery that constructs one:

<!-- litex:skip-test -->
```litex
thm finite_set_has_bijective_index:
    ? forall s finite_set:
        exist idx fn(i range(0, finite_set_size(s))) s st {
            $bijective(range(0, finite_set_size(s)), s, idx)
        }
```

The nearest rejected design introduces module-local predicates such as
`zero_index`, `zero_index_set`, or another spelling of bijectivity. Those
wrappers obscure the standard mathematical interface and force clients to
unfold a `std/basics`-specific definition. The theorem instead depends on the
kernel predicates `$injective`, `$surjective`, and `$bijective`, builtin
finite-set cardinality, and finite-set induction. It is used by constructions
that need a concrete enumeration of an arbitrary finite set. The theorem is
checked; no existence or uniqueness debt remains in its public statement.

## Function mapping properties

Injectivity, surjectivity, and bijectivity are kernel concepts rather than
declarations owned by this module. Their ideal and implemented signatures are:

<!-- litex:skip-test -->
```litex
$injective(A, B, f)
$surjective(A, B, f)
$bijective(A, B, f)
```

Here `A` and `B` are sets and `f : fn(x A) B`. The rejected form is a local
`prop` with the same mathematical body. Kernel ownership gives all modules one
spelling and supports the finite-source consequences used by cardinality
arguments: injections preserve the size of their function range, surjections
bound the finite target size, and bijections preserve size. This module adds no
wrapper or separate proof debt around those facts.

## Divisibility, primality, and greatest common divisors

`divides(a, b)` means that `b = a * k` for some integer `k`. `prime(p)` uses
trial divisors in `range(2, p)`. For a nonzero integer pair, `gcd(a, b)` is the
largest positive common divisor:

<!-- litex:skip-test -->
```litex
prop divides(a Z, b Z):
    exist k Z st {b = a * k}

have fn gcd(a, b Z: a != 0 or b != 0) N =
    finite_set_max({d N_pos: $divides(d, a), $divides(d, b)})
```

The rejected form treats `gcd` only as an unspecified function plus a collection
of axioms. The implemented construction exposes why the result exists: the set
of positive common divisors is finite and nonempty, and the kernel
`finite_set_max` selects its greatest member. This node supports the divisor
laws, Euclidean reduction, Bezout's identity, reduced fractions, and the
prime-divisor dichotomy. The construction and these main laws are checked.

## Reduced rational fractions

`is_reduced_fraction(a, b)` says that an integer numerator and positive
denominator have no positive common divisor other than `1`. The checked
existence theorem is:

<!-- litex:skip-test -->
```litex
thm rational_has_reduced_fraction:
    ? forall q Q:
        exist p Z, d N_pos st {q = p / d, gcd(p, d) = 1}
```

Using a positive denominator is preferable to an unrestricted nonzero integer
denominator because it fixes the sign convention. A separate unique
reduced-fraction theorem is currently trusted; uniqueness is therefore an
explicit proof hole, while ordinary reduced-fraction existence is checked from
the gcd interface.

## Named positive real constants

`pi` and `euler_e` are currently trusted positive real objects. Their ideal
forms remain named real constants backed by mathematical constructions, rather
than predicates that merely recognize an arbitrary value. The constructions
and their characteristic properties are not yet implemented in this module,
so this is an explicit trusted boundary rather than a checked definition.
