# Mathematical Collections: Abstract Algebra

## Purpose and scope

This standalone module models three linked elementary-algebra slices. Group
theory ends at homomorphisms, normal kernels, and finite-group/coset
vocabulary. Commutative-ring theory adds ring homomorphisms, ideals, prime
ideals, and a supplied quotient presentation. Field theory adds integral
domains, fields, and the finite-integral-domain theorem when the existing
finite-set map interface supports its checked proof.

The point is not to accumulate every standard definition. Each slice must
reach one theorem that consumes its objects:

```text
groups -> homomorphism -> kernel -> normal subgroup
rings  -> ideal/prime ideal -> quotient presentation -> prime iff quotient domain
fields -> integral domain -> finite multiplication map -> finite domain is field
```

The module then stops. Sylow theory, group actions and classification,
polynomial rings, Noetherian/PID/UFD theory, the Chinese remainder theorem,
modules and algebras, field extensions, and Galois theory are explicit
non-goals. Algebraic geometry, homological algebra, representation theory,
model theory, and universal algebra are collection-level non-goals rather than
future sections of this module.

## Modeling conventions

The carrier and operations are supplied explicitly. Candidate structures are
relations; reusable theorem contexts are named settings. Existing builtin
sets, functions, equality, and function application remain the underlying
objects. No parallel arithmetic or container interface is introduced.

## Mathematical spine

### Candidate group structure

- **Ordinary meaning:** supplied multiplication, identity, and inverse data
  satisfy the group laws on a nonempty carrier.
- **Semantic role:** Relation testing supplied data.
- **Ideal Litex form:** `prop is_group(...)`.
- **Interface sketch:** `is_group(A, mul, one, inv)` with associativity and
  the standard two-sided identity and inverse clauses.
- **Nearest wrong alternative:** A first-version `struct Group` would force
  every ordinary theorem through field projections even though no theorem
  constructs or transports a group value.
- **Dependencies:** Nonempty sets and function objects.
- **Downstream uses:** `GroupSetting`, cancellation, and uniqueness of identity
  and inverse.
- **Allowable hole:** None in the first checkpoint.

### Group theorem setting

- **Ordinary meaning:** work uniformly in an arbitrary supplied group.
- **Semantic role:** Reusable universal theorem context.
- **Ideal Litex form:** `setting GroupSetting(...)` carrying the group
  parameters and laws, with `prop is_group([GroupSetting])` reusing that
  bundle as the definition-facing interface.
- **Interface sketch:** `forall [GroupSetting], a A: ...`.
- **Nearest wrong alternative:** Repeating every carrier, operation, and law
  in every theorem obscures the mathematical statement.
- **Dependencies:** Candidate group structure.
- **Downstream uses:** Left cancellation and uniqueness of identity and
  inverse.
- **Allowable hole:** None for this interface. Concrete propositions and
  larger settings both consume the same group bundle without repeating its
  parameters or laws.

### Group homomorphism

- **Ordinary meaning:** a supplied function between two groups preserves
  multiplication.
- **Semantic role:** Relation between supplied group data and a function.
- **Ideal Litex form:** `prop is_group_homomorphism([GroupSetting(A, ...)],
  [GroupSetting(B, ...)], f ...)`, consumed through a
  `GroupHomomorphismSetting`.
- **Interface sketch:** the two setting bundles contribute the group laws;
  the relation and theorem setting each add only
  `forall x,y: f(mul_A(x,y)) = mul_B(f(x),f(y))`.
- **Nearest wrong alternative:** A struct-valued homomorphism is unnecessary
  before callers need to pass or project a packaged map and its proof.
- **Dependencies:** Two candidate groups and a function.
- **Downstream uses:** Preservation of identity and inverse, then normality of
  the kernel.
- **Allowable hole:** Images, isomorphisms, and composition remain later work.

### Subgroups, normality, and the kernel

- **Ordinary meaning:** A subgroup contains the identity and is closed under
  multiplication and inverse. It is normal when it is also closed under
  conjugation. The kernel of `f` is the subset `{x A: f(x) = one_B}`.
- **Semantic role:** `is_subgroup` and `is_normal_subgroup` are properties of
  a supplied subset. The kernel used by the flagship theorem is an ordinary
  native set-builder value.
- **Ideal Litex form:** `prop is_subgroup([GroupSetting], H power_set(A))` and
  `prop is_normal_subgroup([GroupSetting], H power_set(A))`.
- **Interface sketch:** `is_normal_subgroup` consumes `is_subgroup` plus
  `forall a A, h H: mul(mul(a,h),inv(a)) in H`.
- **Nearest wrong alternative:** A `Subgroup` struct or a public kernel wrapper
  would package data that no current theorem constructs, passes, or projects.
- **Dependencies:** Group laws, native subsets and set builders, and the two
  homomorphism preservation theorems.
- **Downstream uses:** `kernel_is_normal_subgroup`.
- **Allowable hole:** A full quotient-group construction and the first
  isomorphism theorem remain beyond this version's group stop line.

### Commutative rings and ring homomorphisms

- **Ordinary meaning:** the carrier is an additive abelian group with a
  commutative unital multiplication distributing over addition; a
  homomorphism preserves zero, one, addition, negation, and multiplication.
- **Semantic role:** `CommutativeRingSetting` is the ambient theorem context;
  `RingHomomorphismSetting` composes source and target ring settings with the
  preservation laws.
- **Ideal Litex form:** settings plus the definition-facing projections
  `prop is_commutative_ring([CommutativeRingSetting])` and
  `prop is_ring_homomorphism([RingHomomorphismSetting])`.
- **Nearest wrong alternative:** a `Ring` struct is premature because current
  consumers do not construct or return ring values. Repeating both complete
  law lists in every map theorem obscures the map itself.
- **Dependencies:** native equality and functions; no parallel arithmetic
  object is introduced.
- **Downstream uses:** preservation of zero/negation, kernel is an ideal, and
  quotient presentations.
- **Allowable hole:** noncommutative rings are intentionally outside this
  elementary slice.

### Ideals and prime ideals

- **Ordinary meaning:** an ideal is an additive subgroup absorbing
  multiplication by arbitrary ring elements. A proper ideal is prime when a
  product in it forces one factor into it.
- **Semantic role:** properties of a supplied subset, represented by
  `prop is_ideal([CommutativeRingSetting], I power_set(A))` and
  `prop is_prime_ideal(...)`.
- **Nearest wrong alternative:** a first-class ideal struct would package a
  subset no current theorem stores or projects. Defining primality as “the
  quotient is a domain” would make the flagship equivalence tautological.
- **Dependencies:** commutative-ring laws and native subsets.
- **Downstream uses:** homomorphism kernels and the quotient-domain theorem.
- **Allowable hole:** maximal ideals are named only after a checked theorem
  consumes them; the full maximal-ideal/quotient-field equivalence needs the
  ideal-correspondence or generated-ideal layer and is beyond this version.

### Supplied quotient presentation

- **Ordinary meaning:** a quotient of `A` by `I` is presented by a
  commutative ring `Q` and a surjective ring homomorphism `q : A -> Q` whose
  kernel is exactly `I`.
- **Semantic role:** `setting QuotientRingSetting(...)`; it packages ordinary
  quotient data, not the theorem to be proved.
- **Interface sketch:** two ring settings, `I`, `q`, preservation laws,
  `forall x: x in I <=> q(x)=0_Q`, and surjectivity of `q`.
- **Nearest wrong alternative:** defining the quotient as an arbitrary
  carrier already satisfying “domain iff prime” would smuggle the desired
  result into the interface. Constructing equivalence classes and choice of
  operations locally would add a large representation layer unrelated to the
  theorem's mathematical proof.
- **Dependencies:** ideals, ring homomorphisms, and native existential facts.
- **Downstream uses:** prime ideal iff the supplied quotient is an integral
  domain.
- **Allowable hole:** existence of a quotient presentation for every ideal is
  a separate construction theorem and is not claimed here.

### Integral domains and fields

- **Ordinary meaning:** an integral domain is a nontrivial commutative ring
  with the zero-product property; a field is a nontrivial commutative ring in
  which every nonzero element has a multiplicative inverse.
- **Ideal Litex form:** `prop is_integral_domain([CommutativeRingSetting])` and
  `prop is_field([CommutativeRingSetting])`.
- **Nearest wrong alternative:** putting an inverse function into the base
  ring setting would exclude rings that are not fields and conflate supplied
  data with existential field structure.
- **Dependencies:** commutative-ring laws; the finite theorem additionally
  needs native finite cardinality, function range, injectivity, and preimage
  interfaces.
- **Downstream uses:** the quotient characterization and the finite-domain
  theorem.
- **Allowable hole:** field extensions and Galois theory are beyond the stop
  line.

## Dependency map

```text
nonempty carriers + function objects
  -> is_group                              [definition]
  -> GroupSetting                          [universal context]
  -> cancellation and uniqueness laws      [proof]

two GroupSetting bundles + supplied function
  -> is_group_homomorphism                 [definition]
  -> GroupHomomorphismSetting              [universal context]
  -> preserves identity                    [proof]
  -> preserves inverse                     [proof]
  -> kernel set builder                     [native construction]
  -> subgroup and normal-subgroup laws      [definition]
  -> kernel is normal                       [flagship proof]

two CommutativeRingSetting bundles + supplied function
  -> RingHomomorphismSetting                [universal context]
  -> kernel ideal                           [proof]
  -> ideal / prime-ideal vocabulary         [definitions]

source ring + ideal + target ring + quotient map
  -> QuotientRingSetting                    [surjective map, exact kernel]
  -> prime ideal iff quotient domain        [flagship proof]

finite commutative ring + zero-product law
  -> injective multiplication by nonzero    [proof]
  -> full finite range / preimage of one    [finite-set bridge]
  -> inverse for every nonzero element      [field theorem]
```

## Intended build order

Retain the checked group slice. Then define the commutative-ring setting and
its map setting, prove preservation lemmas and kernel ideality, add ideals and
prime ideals, define a quotient presentation through a surjective map with
exact kernel, and prove the quotient-domain characterization. Add domains and
fields before attempting the finite-domain theorem so its proof consumes the
public interfaces rather than rebuilding them locally.

## Interface decisions and permissible gaps

Settings are the default theorem surface. Introduce a struct only when a real
consumer constructs, transports, compares, or returns a whole algebraic
system. Do not retain both representations through wrappers merely for
convenience.

General quotient construction, maximal-ideal correspondence, modules,
algebras, and extension theory are not permissible hidden trust holes. They
remain explicit non-goals until a later vertical slice is separately designed.
