# Mathematical collections for The Mechanics of Litex Proof

## User-approved builtin teaching convention (2026-10-04)

When the book asks the reader to define a concept that Litex already supplies,
introduce its mathematical definition locally and prove small teaching examples.
Then say explicitly that later work uses the builtin objects. This applies to
quotient/remainder and gcd here; it does not create a fictitious builtin Pascal
or Bezout coefficient function. Pascal remains its original recursive N-valued
function, and Bezout uses an ordinary checked citation theorem.

Sections6.6–6.8 define quotient/remainder and greatest common divisor as
local predicates for teaching, then use `quot(n,d)`, `n%d`, `gcd(a,b)` directly.
The quotient contract is n in Z, d in N+, 0<=r<d. The gcd contract excludes the
pair (0,0). These are explicit builtin contracts: the previous all-integer
source algorithms allowed zero divisors, assigned gcd(0,0)=0 and used a signed
negative-divisor remainder. They are preserved as historical algorithm text,
not asserted to be identical to the builtin contract. Nonzero negative divisors
can use abs(d) with a signed quotient; this keeps the usual division identity.
The mathematical statements about decomposition, remainder bounds, common
divisors and Bezout coefficients remain in the active lesson. The old algorithm
implementation/termination walkthrough is no longer its proof mainline, by the
user's instruction. The complete registered module is verified by the whole-book release gate;
see `experience/problem_notes/2026-10-5-whole-book-run_acceptance.md` in the paired workspace.

## Native number-theory dependencies (audit2026-10-04)

Chapter9 is Sets (`chap9` export) and has no citation dependency. Nine native
facts were checked directly: quotient decomposition, product reordering, gcd
commutativity/zero base/positive carrier/two remainder-zero facts, positive
common divisor bound and remainder range. Their checked ordinary theorem
wrappers do not create native rules or assumptions. Prefer the native facts in
callers; only non-native mathematics needs ordinary proved local interfaces.
The local `divides(d,a)` means `exist k Z st {a=d*k}` and permits d=0. Native
`$dvd(a,d)` reverses arguments and requires d!=0, so replacement must preserve
the source contract. Euclidean gcd recursion and Bezout have no direct rule
established by this audit. The original Chapter7 mathematics now passes10/10 with the checked citation
interfaces. Bezout is proved by strong induction on abs(b), directly constructing
integer coefficients; no recursive coefficient function or added rule is needed.
The original local divides contract is retained. Full Chapter8 pairing passes52/52.
Chapter6 factorial/Pascal and the approved native teaching revision now pass23/23.
The complete export chain is checked by the 2026-10-05 whole-book acceptance.

## Concept-card convention

For each recurring concept, distinguish its ordinary mathematical role, its
Litex interface, the facts that may be inferred from an already-known instance,
and the explicit boundary required to construct a new instance. This prevents
proof convenience from changing the mathematical abstraction.

## Book-wide verification boundary

The executable chapters use the following dependency shape:

```text
known non-forall fact
        |
        v
deterministic builtin computation / one direct builtin rule
        |
        v
structural builtin strategy --smaller constructor--> child known fact / one rule
        |
        v
visible known forall
        |
        v
user-defined strategy

proved definition body --by def--> positive named predicate
proved semantic premises --release thm builtin interface--> concrete object fact
qualified imported theorem --release thm--> local fact or local forall bridge
```

The first chain is automatic atomic verification. The last three arrows are
explicit mathematical interface crossings. A successful domain or
well-definedness check does not promise that every intermediate fact is stored;
persist a carrier or nonzero fact when a later rule genuinely consumes it.

## Defined predicates

Parity, divisibility, primality, function properties, set relations, and named
relations are propositions. Their defining bodies may be conjunctions,
universals, or existentials. Known positive predicate facts still expose their
defining consequences. The reverse direction is explicit:

```litex
claim:
    ? forall x Z:
        $multiple8(x)
        =>:
            $multiple8(5 * x)
    obtain k from $multiple8(x)
    witness $multiple8(5 * x) from 5 * k:
        5 * x = 5 * (8 * k) = 8 * (5 * k)
```

This is a runtime `prop` boundary, not a theorem call or compile-time
expansion. The short form is limited to a concrete definition whose entire
body is one positive ordinary existential fact. A named witness does not target
`exist!`; use explicit `witness exist! ...` and then the separate `by def` fold.
A raw existential, abstract predicate, nested local definition, or definition
with another clause likewise keeps its applicable explicit statement. Negative
instances remain ordinary contradiction proofs. In a named witness proof body,
use the concrete expression supplied after `from`, not the hidden existential
binder's source spelling.

## Arithmetic objects and structural strategies

Numeric carrier and order strategies descend through arithmetic constructors.
For example, a sum is split into its summands and a tuple/cart membership is
split into coordinate memberships. Cross-strategy composition is allowed when
the child has a different constructor family: a Cartesian coordinate such as
`y - z*x` may be discharged by the numeric-carrier strategy.

Arithmetic authoring keeps negative powers explicit. The parser order is
postfix, right-associative power, prefix minus, multiplication/division, then
addition/subtraction, but chapter source writes `-(t^2)` and `(-t)^2` rather
than relying on the bare `-t^2` compatibility parse. Negative exponents use
`t^(-1)`.

A strategy is suitable when each recursive child is a strict syntactic part of
the goal and the same mathematical decomposition remains useful at arbitrary
nesting depth. It is not suitable for a semantic implication such as
`sqrt(t) != 0` via `sqrt(t) > 0` via `t > 0`; a direct rule may consume known
premises but does not chain through another direct rule.

Long iterated objects such as products are treated as mathematical atoms after
their carrier is established. Chapter 7 names repeated products with typed
local values rather than teaching automation a surface alias:

```litex
have prefix_product N+ = product(1, k, fn(x N+) N+ {x})
have next_product N+ = product(1, k + 1, fn(x N+) N+ {x})
```

## Functions

`have fn` supplies a callable value and its defining equation. Function
properties such as injectivity and surjectivity remain `prop` interfaces.
Composition is evaluated one function at a time:

```litex
f_add3_R(x) = x + 3
g_times2_R(f_add3_R(x)) = 2 * f_add3_R(x)
gf_R(x) = g_times2_R(f_add3_R(x)) = 2 * (x + 3)
```

For a compound argument, establish its immediate domain carrier before using a
stored function definition. Tuple extensionality is a semantic object theorem,
not arithmetic normalization:

```litex
release thm tuple_equal_from_coordinates(t, (t[1], t[2]))
```

Compound function concepts are built from the inside out:

```text
inverse equations --by def--> is_inverse
is_inverse --inverse_implies_bijective--> bijective_fn
is_inverse --bodyless witness--> inverse existence
bijective_fn --bijective_implies_has_inverse--> has_inverse
injective body --by def--> injective_fn
surjective body --by def--> surjective_fn
injective + surjective --by def--> bijective_fn
bijection witness --by def--> exist_bijection
```

The directional theorems `inverse_implies_bijective` and
`bijective_implies_has_inverse` are top-level reusable interfaces. A similar
argument kept only as an unnamed `claim` inside a `sketch` is local to that
example and cannot discharge later examples. Once the two inverse equations
are known, a repeated injectivity proof and a repeated surjectivity witness are
translation redundancy rather than new mathematics. The combined `<=>` fact
remains checked in the source example because the current `thm` header does not
accept a forall goal whose body uses `<=>`; the two named directions are its
reusable public surface.

## Sets

A set builder is an object construction. Known membership eliminates to its
base carrier and substituted predicate. Introduction is explicit when those
requirements need full verification:

```litex
release thm set_builder_member(x, {n S: P(n)})
```

Union, intersection, displayed finite-set, set-difference, power-set, and
equality transport continue to use their structural or inference behavior.
Call `set_builder_member` at the first source introduction only; if equality
then transports that membership to another builder, eliminate the transported
fact rather than calling the theorem again.

Subset is a positive builtin definition. Prove the universal membership body,
then write `by def A $subset B`. Extensional equality remains `by extension`
with both membership directions visible.

## Relations

A named relation is a `prop`. Its positive instances are introduced with
`by def` after the relation body is known. The commands `by reflexive_prop`,
`by symmetric_prop`, `by transitive_prop`, and `by antisymmetric_prop` register
checked universal behavior for later use; registration does not fold the
relation definition.

Equivalence classes demonstrate composition of the two explicit interfaces:

```litex
$rel(a2, x)
release thm set_builder_member(x, {b X: $rel(a2, b)})
```

Relation registration proves the predicate premise; the builtin theorem then
introduces the set-builder membership.

## Universal facts and module boundaries

A bare top-level `forall` is appropriate when its body is automatically
verifiable. If the proof requires `by cases`, `by def`, `release thm`, witnesses, or
another proof-control statement, use a `claim` whose goal is that universal
fact.

Automatic known-forall matching uses candidates visible in the current runtime.
Those candidates may come from the current proof scope, an earlier export, or a
referenced imported module. A qualified `release thm` remains preferable when the
dependency should be explicit or automatic matching does not select the
intended theorem. If several nearby steps benefit from the same instance, a
local `claim` forall can make that bridge explicit and reusable.

## Source implementation order

The book's reusable concept dependencies follow this order:

```text
numeric carriers and equality/order rules
  -> parity and divisibility props
  -> induction and finite iteration
  -> prime/gcd interfaces
  -> functions and function properties
  -> set constructors and extensionality
  -> relations, equivalence classes, and bijection relation
```

Later chapters may reuse earlier named theorems either through visible
known-forall matching or explicitly with qualified `release thm`. They must not
duplicate an earlier theorem as a trusted local axiom merely to change the
search route.

## Callable tuple coordinates and stable values

An element of `cart(Z, Z)` has coordinates `u(1)` and `u(2)` and the complete
carrier `finite_seq(Z, 2)`. Coordinate equations retain the original product
mathematics without the retired `u[1]`, `$is_tuple`, or `tuple_dim` interfaces.

The product factor `factorial_factor(x) = x` on `N+` is shared by the divisibility
and Euclid proofs. The functions `real_successor(x) = x + 1` and
`real_square(x) = x^2` are the actual values used by the injectivity lessons.
`multiples_of_four` and `multiples_of_two` own the two set-builder definitions
in the set inequality example. These are exact definitions, with no new axiom
or proof trust.

The class interface is `template<X set, a X>: have equivalence_class set =
{b X: $rel(a, b)}`. A class is a set value indexed by its carrier and
representative, not a function with a dependent parameter domain. The two
checked defining equations expose its membership clauses, and set extension
proves equality of related classes using the original symmetry/transitivity
argument. The equality instance retains the original set-builder meaning.
