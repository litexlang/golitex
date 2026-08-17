# Abstract Algebra

This settings-first group-theory showcase has a checked first checkpoint. It
defines first-class group and group-homomorphism predicates, uses named settings
for ambient theorem contexts, composes the homomorphism setting from two group
bundles, states the standard two-sided group laws, proves cancellation and
uniqueness of identity and inverse, and proves that a homomorphism preserves
identity and inverse. Its flagship theorem then uses the native kernel set
builder to prove that the kernel of a group homomorphism is a normal subgroup.

`main.lit` contains no `trust`. Both the independent release file runner and
module runner return top-level `ok: true`. See `plan.md` and
`math_collections.md` for the fixed scope and interface decisions.
