# Mathematical collections

The compiler ledger exercises one target model: all Litex objects have Lean
type `Litex.Object`, while membership is an independent proposition
`Litex.In object set`.

## Object identity and multiple memberships

The `membership_wd` example is the primary collection. Its object `a` is
introduced with `Litex.In a Litex.C`, later gains
`Litex.In a Litex.R`, and is passed unchanged to an `R`-domain function.
The two proofs coexist; neither changes the Lean type of `a`.

The nearest rejected example omits `a $in R`. Litex rejects the application
before the compiler runs.

## Derived set predicates

`Litex.In` and `Litex.IsSet` form the primitive set boundary. Nonemptiness and
finiteness are derived:

```lean
def Litex.IsNonemptySet (s : Litex.Object) : Prop :=
  Litex.IsSet s ∧ ∃ x : Litex.Object, Litex.In x s

def Litex.IsFiniteSet (s : Litex.Object) : Prop :=
  Litex.IsSet s ∧ Set.Finite {x : Litex.Object | Litex.In x s}
```

The set comprehension here is a Mathlib view of one Litex object's extension,
not a source-level set constructor or a change to the universal-object ABI.
Keeping `Litex.IsSet s` as a conjunct prevents a non-set object with a finite
extension from being accepted as a finite set. A finite set may still be empty.

## Function spaces and application layers

A function space is a `Litex.Object` built from `Litex.FnSpec`. One source
argument group becomes one target list application:

```text
f(1, 2, 3) -> f [1, 2, 3] proof
g(1)(2)    -> (g [1] proof1) [2] proof2
```

The second layer uses `Litex.fnSetResult` to obtain the first result's exact
function-set membership. The nearest rejected form,
`f(1)(2, 3)` for a single three-argument layer, remains a Litex arity error.

## Stored facts and forall replay

The `known_forall` example records an explicit source theorem `FactId`.
Its later use calls that declaration with the ordered object, membership, and
domain proofs. Target-side `assumption` and proposition search are outside
the collection.

## Builtin theorems

The `builtin_theorem` example uses checked not-equality-symmetry and numeral
membership certificates. The generated proof imports the shared Lake module
and calls `Litex.BuiltinRules.notEqualSymmetry`, `numeralInN`, and
`numeralInC`. Concrete rules are neither axioms nor theorem bodies repeated in
generated files.

## Well-definedness identities

Needed application facts are named by `WellDefinedFactId` and emitted before
any theorem whose type contains the proof-carrying application. The primary
example therefore contains a helper proving `Litex.In a Litex.R`, and
`f [a]` cites that helper directly.

Every parsed application also has a `SourceObjectOccurrenceId`. Repeated
textually equal applications retain different source IDs, while a WD cache hit
lets both use edges cite the same `WellDefinedObjProofId` and
`WellDefinedFactId`. Parent/child proof visibility follows the Litex
environment lifetime; malformed or missing occurrence links are rejected
without structural fallback.

## Universal arithmetic and nested forall

The `arithmetic_forall_wd` example keeps `y` as `Litex.Object`, represents
`y - 1` as `Litex.sub y 1`, and calls the proved
`Litex.BuiltinRules.realSubClosure` theorem from structured verifier evidence.
Its nested parameter membership retains the exact temporary `FactId` and is
replayed as a Lean binder proof.

## Trust boundary

The semantic core introduces the universal object universe, membership,
numeric embedding, and restricted application. Concrete builtin rules are
theorems. Only an explicit Litex `trust` statement may become an axiom for a
source proposition. Unsupported proof routes fail closed.
