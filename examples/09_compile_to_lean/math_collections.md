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
f(1, 2, 3) -> f [obj_1, obj_2, obj_3] proof
g(1)(2)    -> obj_4 [obj_5] proof2, where obj_4 := g [obj_1] proof1
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
and calls `Litex.BuiltinRules.notEqualSymmetry`, `numeralInN`, and `numeralInC`.
Concrete rules are neither axioms nor theorem bodies repeated in generated
files.

## Well-definedness identities

Needed application facts are named by `WellDefinedFactId` and emitted before
any theorem whose type contains the proof-carrying application. The feature
ledger's WD DAG entry additionally retains stable `WellDefinedObjId` nodes for
`g(a)`, `t(b)`, and their outer `f` application, with children emitted before
the parent and equal outer occurrences reusing one frozen node.

Every parsed application also has a `SourceObjectOccurrenceId`. Repeated
textually equal applications retain different source IDs, while a WD cache hit
lets both use edges cite the same `WellDefinedObjId` and
`WellDefinedFactId`. Parent/child proof visibility follows the Litex
environment lifetime; malformed or missing occurrence links are rejected
without structural fallback.

## Universal arithmetic and nested forall

The combined showcase's arithmetic-forall route keeps `y` as `Litex.Object`,
represents `y - 1` as `Litex.sub y 1`, and calls the proved
`Litex.BuiltinRules.realSubClosure` theorem from structured verifier evidence.
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

## Statement-object harness basis

The next compiler interfaces should be discovered from a small basis of
executable programs, not from the full Cartesian product of every statement
and object form. Use these rules when extending the feature ledger:

1. Test each statement family first with the cheapest objects: symbols,
   natural numerals, and standard sets.
2. Test each object family first in the cheapest containing statement: a
   reflexive fact or `have name set = object`.
3. Add a cross-family example only when ownership or scope actually interacts,
   such as a named function body, an obtained witness used as an application
   argument, or a set builder used as a return set.
4. Keep candidates here until their complete generated Lean compiles. Move a
   candidate to `compile_to_lean_examples.md` only after its focused positive,
   negative-boundary, malformed-evidence, and real-Mathlib gates pass.

This gives a recommended implementation order. The current result column was
re-audited after implementation on 2026-08-14; it records the established
target recipe and any intentionally narrower boundary.

| Order | Candidate harness | Main pressure | Current result |
| ---: | --- | --- | --- |
| 1 | `inferred_forall_premise` | Rebuild a supported inferred premise inside an existing forall scope | Implemented and recorded in the executable ledger |
| 2 | `object_choice` | One noncomputable object declaration plus its exact stored membership `FactId` | Implemented with `Classical.choose` and exact membership replay |
| 3 | `existential_intro_elim` | Existential binder rendering, witness construction, local names, and ordered projections | Implemented for one positive witness and one body fact; wider forms fail closed |
| 4 | `case_and_contradiction_scopes` | Branch-local and contradiction-local `FactId` scopes without new object constructors | Implemented with local Lean binders and wrong-slot rejection |
| 5 | `named_theorem` | A source name, nested proof steps, the complete forall, and separately stored projections | Implemented with the source theorem name owning its `FactId` |
| 6 | `total_object_constructors` | One uniform renderer path for opaque constants and total set constructors | `pi` and binary `union` implemented as total target objects |
| 7 | `proof_carrying_division` | Two operand memberships plus exact denominator-nonzero evidence | Implemented as a partial Lean constructor consuming all three slots |
| 8 | `proof_carrying_list_set` | Ordered child objects plus a pairwise-distinct construction proof | Implemented in ABI 7 and materialized in the executable ledger with two- and three-entry real-Lean gates |
| 9 | `set_builder_scope` | A binder-owned object, base-set requirement, defining facts, and non-leaking local identity | Implemented with a SymbolId-derived target binder |
| 10 | `named_function` | `HaveFnEqual`, body construction, return membership, definition facts, later application, and definition replay | Implemented with a proof-carrying `functionObject` recipe |
| 11 | `indexed_aggregate` | One representative indexed constructor and projection route before considering sequences and matrices | Implemented for `HaveTupleStmt`; other aggregate families remain explicit boundaries |

The corresponding minimal programs are:

```text
# inferred_forall_premise
forall x R+:
    x > 0

# object_choice
have x R
x $in R

# existential_intro_elim
witness exist x R st {x = 1} from 1:
    1 = 1
obtain y from exist x R st {x = 1}
y = 1

# case_and_contradiction_scopes
by cases:
    ? 1 = 1
    case 1 = 1
by contra:
    ? 2 = 2
    impossible 2 != 2

# named_theorem
thm one_eq_one:
    ? forall:
        1 = 1

# total_object_constructors
pi = pi
forall A, B set:
    union(A, B) = union(A, B)

# proof_carrying_division
forall a, b C:
    b != 0
    =>:
        a / b = a / b

# proof_carrying_list_set
have S set = {1, 2}
S = S

# set_builder_scope
have S set = {x R: x = x}
S = S

# named_function -- the primary integrating tracer
have fn id(x R) R = x
id(1) = 1

# indexed_aggregate
have tuple q for i1 <= 2, q[i1] = 0
q = q
```

The named-function program is the primary integration tracer because it
touches nearly every important boundary, but it should not be the first
implementation. The preceding entries establish forall reconstruction,
declaration ownership, proof scopes, total construction, and proof-carrying
construction separately, so the named-function emitter can reuse evidence
instead of forcing a large speculative interface.

After those basis programs work, add only three deliberate interaction probes:

- an obtained witness used as a named-function argument;
- a `by cases` proof step inside a named theorem;
- a set builder used as a named function's declared return set.

Do not add separate pipeline abstractions for tuples, finite sequences,
matrices, structs, templates, and namespaces yet. First make one indexed
aggregate pass end to end. The remaining forms should either reuse that recipe
or provide concrete evidence that a distinct recipe is necessary.

## Trust boundary

The semantic core introduces the universal object universe, membership,
numeric embedding, and restricted application. Concrete builtin rules are
theorems. Only an explicit Litex `trust` statement may become an axiom for a
source proposition. Unsupported proof routes fail closed.
