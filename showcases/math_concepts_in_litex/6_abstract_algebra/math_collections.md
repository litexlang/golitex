# Mathematical Collections: Abstract Algebra

## Purpose and scope

This standalone first version models the theorem-facing core of elementary
group theory. It is for readers learning how Litex represents an ambient
mathematical structure without requiring that structure to be passed as a
first-class record. The flagship theorem proves that the kernel of a group
homomorphism is a normal subgroup. Rings, modules, quotients, actions, and
classification results are outside this checkpoint.

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
- **Allowable hole:** Cosets, quotient groups, and the first isomorphism
  theorem remain later work.

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
```

## Intended build order

Define the candidate group relation, expose its setting, prove cancellation
and the identity/inverse uniqueness toolkit, define the homomorphism relation
and setting, prove identity and inverse preservation, then use the native
kernel set builder to prove the kernel is a normal subgroup.

## Interface decisions and permissible gaps

Settings are the default theorem surface. Introduce a struct only when a real
consumer constructs, transports, compares, or returns a whole algebraic
system. Do not retain both representations through wrappers merely for
convenience.
