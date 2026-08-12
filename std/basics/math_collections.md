# Mathematical design of `std/basics`

`std/basics` contains small source-level interfaces that are reused across
otherwise independent developments. It should not wrap concepts that already
belong to the Litex kernel. The declarations below are the main mathematical
nodes that determine the module's current shape.

## Finite subsets

Mathematically, every subset of a finite set is finite. This foundational fact
is now a reserved bare kernel theorem rather than a `std/basics` declaration:

<!-- litex:skip-test -->
```litex
by thm subset_of_finite_set_is_finite(A, B)
```

The call requires `A` to be a set, `B` to be finite, and the explicit premise
`A $subset B`; it stores `$is_finite_set(A)`. The rejected design is automatic
subset-chain search: knowing only `A $subset B` and `B $subset C` does not
silently derive finiteness. Downstream clients such as the finite common-divisor
construction call the theorem at the exact mathematical step where it is used.

## One-based indexing of finite sets

A finite set `s` of size `n` admits an enumeration by a bijection from
`closed_range(1, n)`. The reserved bare kernel interface is existential because
clients need an indexing function, not a canonical choice:

<!-- litex:skip-test -->
```litex
by thm finite_set_has_bijective_index(s)
# stores:
exist idx finite_seq(s, finite_set_size(s)) st {
    $bijective(closed_range(1, finite_set_size(s)), s, idx)
}
```

`finite_seq(S,n)` accepts `n : N`, including `[] : finite_seq({},0)`. For
function-property checks, exactly its internal type `fn(i N+: i <= n) S`
bridges to `closed_range(1,n)`; nearby ranges do not. An arbitrary member of a
finite-sequence space is not automatically bijective—the theorem supplies one
chosen witness. The rejected designs are module-local indexing predicates,
zero-based source wrappers, and any uniqueness claim for the enumeration.

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

`divides(a, b)` means that `b = a * k` for some integer `k`. Native `$prime(p)`,
`$coprime(a, b)`, and `gcd(a, b)` are the directly usable interfaces. Following
Mathlib's elementary-number-theory layer, `$prime` has carrier `N` and
`$coprime` has carrier `N x N`; the latter is the total gcd-one predicate, so
`(0,0)` is false and `(0,1)` is true. The module retains the transparent
trial-division predicate, but does not expose a second gcd function or a
source-level duplicate of coprimality:

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
still identify trial-division primality with `$prime`. Positive `$coprime`
facts expose the non-all-zero condition required by the native partial `gcd`
object and then `gcd(a,b)=1`. This node supports the divisor laws, Euclidean
reduction, Bezout's identity, reduced fractions, and the prime-divisor
dichotomy.

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
