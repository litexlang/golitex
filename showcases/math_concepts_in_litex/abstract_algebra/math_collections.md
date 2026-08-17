# Mathematical Collections: Abstract Algebra

## Purpose and scope

This standalone first version models the theorem-facing core of elementary
group theory. It is for readers learning how Litex represents an ambient
mathematical structure without requiring that structure to be passed as a
first-class record. Rings, modules, quotients, actions, and classification
results are outside this checkpoint.

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
- **Interface sketch:** `is_group(A, mul, one, inv)` with associativity, left
  identity, and left inverse clauses.
- **Nearest wrong alternative:** A first-version `struct Group` would force
  every ordinary theorem through field projections even though no theorem
  constructs or transports a group value.
- **Dependencies:** Nonempty sets and function objects.
- **Downstream uses:** `GroupSetting`, cancellation, and inverse laws.
- **Allowable hole:** None in the first checkpoint.

### Group theorem setting

- **Ordinary meaning:** work uniformly in an arbitrary supplied group.
- **Semantic role:** Reusable universal theorem context.
- **Ideal Litex form:** `setting GroupSetting` carrying the group parameters
  and laws directly. The first-class `is_group(...)` proposition remains the
  definition-facing interface.
- **Interface sketch:** `forall [GroupSetting], a A: ...`.
- **Nearest wrong alternative:** Repeating every carrier, operation, and law
  in every theorem obscures the mathematical statement.
- **Dependencies:** Candidate group structure.
- **Downstream uses:** Left cancellation, right identity, and right inverse.
- **Allowable hole:** Settings cannot appear in definitions or object
  expressions. In the current elaborator, a proposition call inside a setting
  is accepted at declaration time but becomes unparsable when expanded in a
  theorem header, so the setting repeats the laws directly.

### Group homomorphism

- **Ordinary meaning:** a supplied function between two groups preserves
  multiplication.
- **Semantic role:** Relation between supplied group data and a function.
- **Ideal Litex form:** `prop is_group_homomorphism(...)`, consumed through a
  `GroupHomomorphismSetting`.
- **Interface sketch:** the relation contains both group facts and
  `forall x,y: f(mul_A(x,y)) = mul_B(f(x),f(y))`.
- **Nearest wrong alternative:** A struct-valued homomorphism is unnecessary
  before callers need to pass or project a packaged map and its proof.
- **Dependencies:** Two candidate groups and a function.
- **Downstream uses:** Preservation of identity and inverse.
- **Allowable hole:** Kernels, images, isomorphisms, and composition remain
  later work.

## Dependency map

```text
nonempty carriers + function objects
  -> is_group                              [definition]
  -> GroupSetting                          [universal context]
  -> cancellation and right-side laws      [proof]

two is_group facts + supplied function
  -> is_group_homomorphism                 [definition]
  -> GroupHomomorphismSetting              [universal context]
  -> preserves identity                    [proof]
  -> preserves inverse                     [proof]
```

## Intended build order

Define the candidate group relation, expose its setting, prove the minimal
cancellation/right-law toolkit, define the homomorphism relation and setting,
then prove identity and inverse preservation.

## Interface decisions and permissible gaps

Settings are the default theorem surface. Introduce a struct only when a real
consumer constructs, transports, compares, or returns a whole algebraic
system. Do not retain both representations through wrappers merely for
convenience.
