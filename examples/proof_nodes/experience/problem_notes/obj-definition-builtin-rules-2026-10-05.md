# Elementary Obj definition rules

Task context: the user asked for a per-Obj check of missing defining/basic
properties, then approved adding the ordinary local builtin rules found by
that check. Scope: floor/ceil bounds, tan/cot quotients, gcd Euclidean recursion,
and usable finite-extremum member bounds in the current Rust kernel.

## Former direct inputs and diagnosis

The rebuilt baseline rejected all six journal inputs with exit 1 and top-level
`success: false`. Normal reported `search_proof` for each whole forall.
The [journal](../../proof_journals/obj-definition-builtin-rules-2026-10-05.json)
retains exact source, binary fingerprint and raw output. No trust was added.

```litex
forall x R:
    floor(x)<=x
    x<floor(x)+1
    ceil(x)-1<x
    x<=ceil(x)

forall x R:
    cos(x)!=0
    =>:
        tan(x)=sin(x)/cos(x)

forall x R:
    sin(x)!=0
    =>:
        cot(x)=cos(x)/sin(x)

forall a Z,b N+:
    gcd(a,b)=gcd(b,a%b)

forall S finite_set,x S:
    $is_nonempty_set(S)
    S $subset R
    =>:
        x<=finite_set_max(S)
        finite_set_min(S)<=x
```

The first four families lacked exact local defining leaves. Finite-extremum
member-order leaves already existed. Their bounded carrier consumers lacked
intrinsic real codomains and one-step transport from stored `x $in S` and
`S $subset R`. Source inspection and the focused Direct-level tests establish
this narrower carrier gap; the whole-forall Normal label alone does not
identify that internal phase.

## Local implementation and evidence

- `rounding_definition_bounds.rs` supplies independent FloorLowerBound,
  FloorStrictUpperBound, CeilStrictLowerBound and CeilUpperBound proofs.
- `by_elementary_definitions.rs` supplies independent TanQuotientDefinition,
  CotQuotientDefinition and GcdEuclideanStep proofs; equality may be written
  in either direction. All repeated arguments must match exactly.
- Parent WD retains real rounding/trig domains, nonzero trig denominators,
  integer gcd inputs and the nonzero remainder divisor. The gcd step also
  works with a signed nonzero integer divisor.
- Structural membership adds the intrinsic real codomains of checked finite
  max/min. KnownSubsetMembershipProof retains both actual atomic premise
  citations. Its lookup reads visible stored facts/equality paths only; it
  does not prove an intermediate membership/subset or invoke truth/WD search.
- Existing FiniteSetMaxMemberLe / FiniteSetMinMemberLe proofs still retain
  their member premise. No AST, Env, Runtime or VerifyState fields changed.

Each new builtin leaf owns ten localized texts and a distinct Detailed rule
identity. Structural carrier output retains its intrinsic rule or both stored
premises. Tests project the actual executed then-fact through Normal's atomic
consumer; whole-forall Normal output continues to show its compound label.

The current crate has no `crate::prelude` module. New modules use the existing
neighboring explicit imports rather than introducing an unrelated prelude.

## Acceptance

Focused release tests passed:

```text
cargo test --release --offline obj_definition_builtins_tests -- --nocapture
    7 passed
cargo test --release --offline search_structural_membership::tests -- --nocapture
    7 passed
cargo test --release --offline builtin_entry_policy_tests -- --nocapture
    13 passed
```

The 27 tests cover exact typed winners, both equality directions, valid
carriers, all ten Normal/Detailed language consumers, retained membership and
subset citations, Direct permission ceilings, no evidence publication during
Direct search, failed theorem scope cleanup, and nearest false/domain cases.
Rejected controls include strict inequalities at integer rounding boundaries,
wrong rounding directions or arguments, absent trig guards, swapped trig
quotients, zero remainder divisors, noninteger gcd inputs, empty/nonreal extrema,
unrelated members/subsets and an attempted uncited two-edge transport at Direct.

Five before/now/boundary tracers and seven owning Obj files are the final CLI
gates. P200 is registered in each corresponding Obj coverage entry.
Run each file with `target/release/litex -strict -f <path>`; require exit 0 and
top-level `success: true`. The current CLI has no `-compact`, `-runner`,
`-before` or literal `try:` interface, so those older workflow flags were
not used.

Final build succeeded. All twelve whole-file CLI gates returned exit 0 and
top-level `success: true`; the complete source/Cargo fingerprint stayed stable
from before the build through the last gate. Binary SHA256:
`1b9b13819f42a6c7ce9f03f59a500033582abd1fcb6408f5a565beae685fa927`.
The journal retains all whole-file output, the three exact focused test runs,
and intermediate harness failures (forall Normal summarization and a top-level
unproved setup premise), followed by their corrected actual-consumer gates.

No complete examples/module/release sweep, independent certificate replay or
Lean gate is claimed. Reuse lesson: a defining truth rule should consume the
existing checked object domain; an already present order rule may instead need
a local carrier interface at its bounded consumer.
