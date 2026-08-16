# Mathematical collections

The compiler ledger exercises one target model: all Litex objects have Lean
type `Litex.Object`, while membership is an independent proposition
`Litex.In object set`.

## Object identity and multiple memberships

The combined showcase's membership route introduces object `a` with
`Litex.In a Litex.C`, then gains
`Litex.In a Litex.R`, and is passed unchanged to an `R`-domain function.
The two proofs coexist; neither changes the Lean type of `a`.

The nearest rejected example omits `a $in R`. Litex rejects the application
before the compiler runs.

## Derived set predicates

`Litex.In` and `Litex.IsSet` form the primitive set boundary. Nonemptiness and
finiteness are derived:

```lean
def Litex.IsNonemptySet (s : Litex.Object) : Prop :=
  ∃ x : Litex.Object, Litex.In x s

def Litex.IsFiniteSet (s : Litex.Object) : Prop :=
  Set.Finite {x : Litex.Object | Litex.In x s}
```

The set comprehension here is a Mathlib view of one Litex object's extension,
not a source-level set constructor or a change to the universal-object ABI.
Every `Litex.Object` is set-like definitionally, so a separate conjunct would
be redundant. A finite set may still be empty.

## Function spaces and application layers

A function space is a `Litex.Object` built from `Litex.FnSpec`. One source
argument group becomes one target list application:

```text
f(1, 2, 3) -> f [1, 2, 3]
g(1)(2)    -> (g [1]) [2]
```

The second layer uses `Litex.fnSetResult` to obtain the first result's exact
function-set membership. The nearest rejected form,
`f(1)(2, 3)` for a single three-argument layer, remains a Litex arity error.

## Stored facts and forall replay

The executable feature ledger records an explicit trusted universal theorem
`FactId`. Its later atomic use calls that declaration with the ordered object
and membership proof. The combined showcase additionally covers domain proofs.
Target-side `assumption` and proposition search are outside the collection.

## Builtin theorems

The shared-builtin tracer uses checked not-equality-symmetry and numeral
membership certificates. The generated proof imports the shared Lake module
and calls `Litex.Rules.notEqualSymmetry`, `numeralInN`, and `numeralInC`.
Concrete rules are neither axioms nor theorem bodies repeated in generated
files.

## Well-definedness identities

Needed application facts are named by `WellDefinedFactId` after the binders of
the theorem that owns them. The feature ledger's WD DAG entry additionally
retains stable `WellDefinedObjId` nodes for `g(a)`, `t(b)`, and their outer `f`
application. Local WD, applicability, and result-membership steps are replayed
child-before-parent, while the theorem type contains only proof-free object
terms; equal outer occurrences reuse one frozen node.

Every parsed application also has a `SourceObjectOccurrenceId`. Repeated
textually equal applications retain different source IDs, while a WD cache hit
lets both use edges cite the same `WellDefinedObjId` and
`WellDefinedFactId`. Parent/child proof visibility follows the Litex
environment lifetime; malformed or missing occurrence links are rejected
without structural fallback.

## Universal arithmetic and nested forall

The combined showcase's arithmetic-forall route keeps `y` as `Litex.Object`,
represents `y - 1` as `Litex.sub y 1`, and calls the proved
`Litex.Rules.realSubClosure` theorem from structured verifier evidence.
Its nested parameter membership retains the exact temporary `FactId` and is
replayed as a Lean binder proof.

## Statement definitions

The combined showcase's statement-definition route separates four target roles:

- `abstract_prop` introduces an uninterpreted `Litex.Object → Prop`;
- a bodyful `prop` is a Lean definition whose body contains parameter
  requirements and source clauses;
- `have name S = value` introduces one `noncomputable def` plus checked
  membership and defining-equality theorems;
- `by def` constructs or projects the definition conjunction from exact child
  proofs and `FactId` citations.

Only the example's explicit `trust` fact is an axiom. Its later repetition and
all inferred definition consequences reuse or derive named theorems. Bodyless
concrete `prop`, `trust have`, and function-valued `have fn` are deliberately
outside this collection.

## Statement and object coverage

The ledger currently covers the following statement and object interactions:

| Capability | Current target representation | Current boundary |
| --- | --- | --- |
| Inferred universal premise | A local theorem registered by its exact `FactId` | Unsupported inference chains fail closed |
| Object choice | `Classical.choose` plus its exact membership theorem | Choice requires retained nonemptiness evidence |
| Existential introduction and elimination | One existential theorem followed by ordered witness projections | Wider projection shapes remain explicit boundaries |
| Cases and contradiction | Local Lean binders scoped to the source proof branch | Branch-local facts cannot escape their scope |
| Named theorem | The source theorem name owns the complete universal fact | Missing child facts are not reconstructed by target search |
| Total constructors | Closed `pi` and binary `union` object terms | Partial source constructions use proof-free terms plus separate WD recipes |
| Division | Two numeric memberships plus denominator nonzero evidence | A missing or retargeted proof slot is rejected |
| Finite set literal | Ordered child objects and the full pairwise-distinctness matrix | Missing, reversed, or duplicated pairs are rejected |
| Set builder | A `SymbolId`-owned predicate binder | The binder cannot leak outside the builder |
| Named function | Checked body, range closure, function-set membership, definition equality, and later application | Unsupported body evidence fails closed |
| Indexed tuple | A checked dimension and coordinate recipe | Other aggregate families are not implied by this representation |
| Anonymous function | A scoped `functionObject` with checked return membership | A body outside the declared result set is rejected |
| Known equality path | Direct `Eq.symm` and `Eq.trans` calls from stored equality facts | The compiler does not search for a replacement path |

The combined interaction entry contains three cross-family compositions:

- an obtained witness used as a named-function argument;
- a case proof inside a named theorem;
- a set builder used as a named function's declared return set.

These interactions reuse the same object, scope, and proof-evidence interfaces
as the individual entries; they do not introduce interaction-specific axioms.

## Trust boundary

The semantic core introduces the universal object universe, membership,
numeric embedding, and restricted application. Concrete builtin rules are
theorems. Only an explicit Litex `trust` statement may become an axiom for a
source proposition. Unsupported proof routes fail closed.
