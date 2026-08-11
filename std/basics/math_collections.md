# Mathematical design of `std/basics`

`std/basics` contains small source-level interfaces that are reused across
otherwise independent developments. It should not wrap concepts that already
belong to the Litex kernel. The declarations below are the main mathematical
nodes that determine the module's current shape.

## Finite subsets

Mathematically, every subset of a finite set is finite. This fact is needed to
construct bounded sets such as the positive common divisors of two integers.
Its current Litex form is a named checked standard-library theorem:

<!-- litex:skip-test -->
```litex
thm subset_of_finite_set_is_finite:
    ? forall A set, B finite_set:
        A $subset B
        =>:
            $is_finite_set(A)
    A = set_minus(B, set_minus(B, A))
    $is_finite_set(set_minus(B, set_minus(B, A)))
    $is_finite_set(A)
```

The nearest rejected form is a dedicated finite-subset builtin rule. The theorem
instead uses the narrower builtin identity that recovers a subset as a double
relative complement, together with finite set difference. It depends only on
builtin set membership, subset, equality, and finite-set predicates; downstream
users include the finite common-divisor set used to define `gcd`.

## Zero-based indexing of finite sets

A finite set `s` of size `n` admits an enumeration by a bijection from
`range(0, n)`. The public interface is existential because clients need an
indexing function, not the induction machinery that constructs one:

<!-- litex:skip-test -->
```litex
thm finite_set_has_bijective_index:
    ? forall s finite_set:
        exist idx fn(i1 range(0, finite_set_size(s))) s st {
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

## Euclidean quotient selection

For an integer `a` and positive integer `d`, Euclidean division determines one
integer `q` satisfying `a = d * q + a % d`. The module exposes that selected
value as an ordinary source function:

<!-- litex:skip-test -->
```litex
have fn integer_quotient by exist!:
    ? forall a Z, d N+:
        exist! q Z st {a = d * q + a % d}
```

The rejected form is a dedicated `IntegerQuotient` kernel object and reserved
parser token. The kernel now owns only the narrow unique-existence fact; the
name, function object, defining equation, and namespace remain inspectable
source-level data. Clients import this module and write
`basics::integer_quotient`, while a textbook may own the same small selection
locally when that better preserves its dependency structure.

## Divisibility, primality, and greatest common divisors

`divides(a, b)` means that `b = a * k` for some integer `k`. Native `$prime(p)`
and `gcd(a, b)` are the directly usable interfaces. The module retains the
transparent trial-division predicate, but does not expose a second gcd
function:

<!-- litex:skip-test -->
```litex
prop prime_by_trial_division(p N+):
    2 <= p
    forall d range(2, p):
        p % d != 0
```

The rejected standard-library form is a parallel source function such as
`gcd_by_finite_divisors`. User code should not have to choose between two gcd
objects. The checked public theorems instead build directly on the native
contract: positivity, divisibility of both arguments, and maximality among
positive common divisors.

The separate teaching example
[`gcd_from_finite_divisors.lit`](../../examples/04_case_studies/gcd_from_finite_divisors.lit)
shows that the set of positive common divisors is finite and nonempty, selects
its greatest member with `finite_set_max`, and proves the result equal to native
`gcd`. Keeping that construction outside the module preserves its explanatory
value without making it a competing public interface. Checked bridge theorems
still identify trial-division primality with `$prime`. This node supports the
divisor laws, Euclidean reduction, Bezout's identity, reduced fractions, and
the prime-divisor dichotomy.

Native `lcm` follows the dual public pattern: the object and its primitive
remainder/minimality rules remain in the kernel, while checked source theorems
connect them to the transparent `divides` predicate. For positive inputs the
module exports left and right divisibility and the least-positive-common-
multiple theorem. The same quotient witness pattern exposes the native
factorial remainder law as `earlier_factorial_divides_later`.

## Native monotone and sign interfaces

Strictly monotone native objects must be usable in both directions. The kernel
therefore owns exp/ln order preservation, order reflection, and injectivity;
this module gives the reflection directions stable theorem names. The sign
object similarly owns its algebra and zero/nonzero characterization in the
kernel, with named checked bridge theorems here. These are wrappers around
mathematical consequences, not competing source-defined functions.

## Reduced rational fractions

`is_reduced_fraction(a, b)` says that an integer numerator and positive
denominator have no positive common divisor other than `1`. The checked
existence theorem is:

<!-- litex:skip-test -->
```litex
thm rational_has_reduced_fraction:
    ? forall q Q:
        exist p Z, d N+ st {q = p / d, gcd(p, d) = 1}
```

Using a positive denominator is preferable to an unrestricted nonzero integer
denominator because it fixes the sign convention. The unique canonical form is
owned by the kernel and can be requested with the reserved bare call
`by thm rational_has_unique_reduced_fraction(q)`. It returns
`exist! p Z, d N+ st {q = p / d, gcd(p, d) = 1}`; no trusted `std/basics`
wrapper is involved. Ordinary source-level existence remains checked here from
the gcd interface.

## Named positive real constants

`e` and `pi` are native positive real constants. They are direct scalar
objects, rather than source-level declarations or predicates that recognize an
arbitrary value. Their carrier and positivity facts come from the kernel; this
module does not duplicate them with trusted declarations.
