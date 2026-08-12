# Litex-to-Lean compiler and IR MVP

Litex-to-Lean no longer re-reads a verified source statement and guesses a tactic
from its syntax. The verifier produces a backend-facing proof IR; the Lean
emitter accepts only that IR.

## Execution contract

`Runtime` has an explicit `litex_to_lean_ir_mode` flag.

- Every fact admitted by runtime storage to an environment's known-fact cache
  receives a runtime-unique `FactId`, in ordinary execution as well as compiler
  execution. Display, nested-binder, and alpha-normalized cache aliases for one
  stored fact share the same ID.
- Ordinary execution leaves `StmtResult::litex_to_lean_ir()` as `None`.
- Litex-to-Lean mode attaches `Some(LitexToLeanStatementIr)` only after successful statement
  execution. Fact IR is assembled after storage, so its citations can carry
  stable IDs rather than matching later by display text.
- Local proof premises are distinguished from trusted facts. When a local
  premise was stored in a temporary environment, its ID survives in the
  returned proof IR. The emitter maps it to a proof-space coordinate such as
  `proof_fact_2_3`; that coordinate is not the temporary Litex `FactId`.

The environment cache deliberately stores only `FactId` plus the existing
source location. Proof trees, origins, inferred consequences, local/global Lean
names, and recursive dependencies live in statement results and Litex-to-Lean IR.

### Complete and incomplete return values

`compile_to_lean_with_report` is the partial-compilation entrypoint. It returns a
`LitexToLeanCompilationReport` whose `status` is either `Complete` or `Incomplete`,
whose `lean_code` is always the checked subset that the backend could emit, and
whose `unsupported` list identifies every omitted statement by source index,
rendered statement, path, line, compiler phase, and reason.

Parsing errors, runtime errors, and unverified Litex statements still return
`Err`: those inputs never established a verified source program. Once a
statement has verified, lack of compiler IR or lack of a checked Lean backend
becomes an `Incomplete` diagnostic instead. Report mode continues through later
statements so independent supported declarations are not lost.

Lean emission is transactional per source statement. The emitter checkpoints
its declarations, global `FactId` set, and local-name allocator before lowering
one statement. If any nested proof or inferred fact is unsupported, that whole
statement is rolled back and replaced by a Lean line comment containing the
same diagnostic. It never leaves half of a multi-fact statement behind and
never substitutes `axiom` or `sorry`. The generated source starts with a
machine-readable reader cue such as `-- Litex-to-Lean status: incomplete`.

The existing `compile_to_lean`, `compile_to_lean_from_source`, and `emit_lean_from_litex_to_lean_ir` entrypoints
remain strict and fail closed. Their report counterparts are
`compile_to_lean_with_report`, `compile_to_lean_from_source_with_report`, and
`emit_lean_from_litex_to_lean_ir_with_report`.

## Rust API naming

Names follow the architectural boundary they describe:

- `compile_to_lean` is the action-oriented compiler module and function prefix.
- `litex_to_lean_ir` is the verifier-produced bridge IR module and field prefix;
  it is not Lean's own intermediate representation.
- Public bridge types use the `LitexToLean<Domain>Ir` shape, such as
  `LitexToLeanStatementIr` and `LitexToLeanFactIr`. The domain noun comes before
  the `Ir` qualifier so the name reads as the IR representation of that domain.
  Compiler outcomes use `LitexToLeanCompilation...` instead.

### Naming migration tracer

- Before: `LitexToLeanIrStatement`, `LitexToLeanIrFact`, and
  `StmtResult::to_lean_ir: Option<StmtToLeanIR>`.
- Now: `LitexToLeanStatementIr`, `LitexToLeanFactIr`, and
  `StmtResult::litex_to_lean_ir: Option<LitexToLeanStatementIr>`.
- Boundary: modules, fields, and construction functions retain the
  `litex_to_lean_ir` phrase because they name the bridge layer or an action;
  only IR value types follow the suffix rule. These are intentional breaking
  API renames, and the old names are not retained as aliases.
- Evidence: run
  `cargo test --release compile_to_lean::pipeline::tests::litex_to_lean_ir_preserves_fact_ids_and_verified_routes -- --nocapture --exact`
  and
  `target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/litex_to_lean_ir_mvp.lit`.

## Environment and proof-scope correspondence

A proof-relevant temporary Litex environment is a semantic scope boundary, not
merely a verifier implementation detail. Whenever verification opens a child
environment and the selected successful route depends on facts introduced or
derived there, the returned `StmtResult` must preserve those facts and their
derivations inside one recursively nested proof unit. It must not leak their
temporary `FactId`s into the parent scope or flatten the result into a global
citation that forgets how the local work was performed.

Within the supported slice, Litex-to-Lean lowers that proof unit into a corresponding
nested Lean proof scope, normally a `by` block containing local `intro`, `let`,
`have`, or a theorem-like local lemma. The scope inherits exactly the parent
evidence that was visible to the Litex child environment; facts created inside
it remain local. If a supported local verification step itself opens another
environment and packages several steps before producing a usable fact, its IR
contains another nested proof unit and Lean emits another nested proof scope.
Thus environment nesting determines proof encapsulation and dependency
visibility, even though Litex environments and Lean syntax are not represented
by identical data types.

`ForallIntroduction` is one concrete example: parameters and premises installed
in its temporary environment survive in the returned proof IR, then become
Lean binders and local `proof_fact` names. A nested known-forall application
similarly becomes a local `have ... := by ...` with its own `proof_arg` and
requirement proofs. `CaseSplit` and `ByContradiction` now provide two more
concrete examples: branch assumptions and the reverse assumption retain their
temporary `FactId`s and are installed only in the corresponding Lean proof
scope. The MVP does not yet serialize every runtime environment as a
general-purpose IR node. Purely operational search environments whose branches
were not selected need not be serialized; the invariant applies to every
environment boundary on the successful proof route. If such a proof-relevant
route has no supported nested representation, compilation must stop instead of
flattening away the scope.

## Statement and proof IR

The MVP currently constructs nine statement forms:

- `AbstractProp`
- `Prop`
- `Trust`
- `Fact`
- `HaveObjChoice`
- `HaveObjEqual`
- `HaveExistentialWitness`
- `Proof`
- `ProjectedForall`

A fact contains its proposition, optional stored `FactId`, and a recursive
`LitexToLeanFactProofIr`. Direct citations are proof-tree leaves. Derived facts use
one general `RuleApplication { rule, parameter_requirements, premises }` node,
so a new transport method extends `LitexToLeanProofRuleIr` without changing the
recursive proof-tree shape. The first rule vocabulary contains equality and
iff rewrite, definition reduction, checked definition projection,
normalization, known-forall instantiation,
modus ponens, conjunction/existential introduction, case split, and an explicit
unsupported rule. Only equality rewrite, definition reduction, the supported
normalization slice, known-forall instantiation, and the structured quotient-
nonzero, not-equality symmetry, subset/superset duality, closed-u64 prime
reflection, standard numeric-set membership projection, and 86 registered
local schemas—including 20 elementary real arithmetic/order rules—currently
have Lean backends. Positive existential
introduction is also checked
from its retained witness, parameter requirements, local proof steps, and
direct body proofs.

`ProjectedForall` preserves the runtime's clause-coverage behavior. When one
source universal has independently covered conclusions, the runtime may store
smaller universal facts rather than assign one `FactId` to the source-wide
conjunction. Litex-to-Lean retains those exact stored propositions and IDs, filters
the recorded parameter premises to each retained binder set, and reuses the
matching checked conclusion proofs. A genuinely multi-conclusion stored
universal instead emits a native Lean conjunction whose components are proved
in source order. Neither route invents a synthetic ID for an unstored source
fact.

### Object definitions, existential witnesses, checked choice, and scoped proof commands

The first statement-effect tranche supports explicit object definitions and
two proof commands without treating source syntax as a Lean tactic script.

For `have x R = 2`, runtime lowering validates the exact stored membership and
defining-equality facts, preserves their `FactId`s, and produces one
`LitexToLeanObjectDefinitionIr` plus its proof facts. At file scope Lean receives a
`def x : ℝ := 2`; inside a proof it receives a scoped `let`. The defining
equality is checked by `rfl`. The membership proof first checks the right-hand
side and then transports it through the named definition with `simpa only
[x]`. No new axiom supplies either fact.

For bare `have selected R`, runtime returns an explicit mapping from the
checked `$is_nonempty_set(R)` result to the exact stored
`selected $in R` fact. `HaveObjChoice` freezes that proof, the selected
`SymbolId`, the carrier, and the membership `FactId`. In the target ABI,
`litexIsNonemptySet s` is definitionally `Set.Nonempty s`, so file-scope
selection becomes a `noncomputable def` built with `Exists.choose`, and its
membership theorem is `Exists.choose_spec` from the same named certificate.
Inside a proof, the certificate, selected value, and membership remain local
`have`/`let` bindings. The currently checked builtin source is the real
carrier; a previously emitted nonemptiness fact may also serve as the exact
certificate when its proof route has a backend. No opaque constant or generated
axiom supplies the value.

For `witness exist u R st {...} from e`, execution retains the concrete
witness-type checks before temporary existential binders enter scope, together
with the user proof steps and one checked result per direct body fact. The
compiler emits a theorem whose proposition is a nested Lean `Exists` package
and constructs it from exactly those proofs. Closed numeric propositions are
given one fact-level native carrier when needed, so division cannot silently
default to `Nat` while the existential expects a rational or real witness.

For `witness $P(args) from values`, execution retains a distinct named-witness
statement and freezes the active concrete definition plus its instantiated
plain `exist` clause. Runtime lowering first builds the same checked
`ExistIntroduction` proof as the explicit form, then wraps it in a
`DefinitionIntroduction` node whose source and target are both frozen. The
emitter checks the sole premise, positive existential source, positive named
prop target, and definition name before emitting `simpa only [P] using source`.
It does not query the runtime definition table. The stored primary fact remains
`$P(args)`; the ordinary definition consequence is emitted through the checked
reverse `DefinitionProjection` edge.

`obtain w from exist ...` and body-style `have w R: ...` then lower through
`HaveExistentialWitness`. The node contains the checked source existential,
fresh witness `SymbolId`s and instantiated parameter types, and every exact
stored type/body projection with its `FactId`. File-scope witnesses are
`noncomputable def`s built by ordered, possibly nested `Exists.choose`; proof-
local witnesses are `let`s. Type and body facts come only from the matching
`Exists.choose_spec` projections. Citations of the same existential under
fresh binder IDs use an explicit alpha-renaming citation node admitted only
after the verifier's canonical existential comparison succeeds. No trust,
opaque declaration, compiler-created axiom, or `sorry` supplies a witness.
When the source syntax is `obtain w from $P(args)`, the verifier retains a
`DefinitionProjectionBuiltinRuleEvidence` containing the positive prop call
and its concrete definition. Runtime lowering re-instantiates the definition,
requires its sole clause to be the exact positive existential target, and
requires one recursive proof of `$P(args)`. The resulting
`DefinitionProjection` proof IR freezes both expected propositions. The pure
emitter checks those fields and emits `simpa only [P] using source`; Lean then
kernel-checks the definition unfolding before the normal `Exists.choose` and
`choose_spec` path runs. No diagnostic label is used as compiler evidence.
Before rendering an `exist` or `forall`, the emitter also compares binder and
occurrence `SymbolId`s after Lean-name sanitization. If distinct Litex names
would collapse to one Lean identifier and capture each other, compilation
fails with a rename diagnostic instead of changing the proposition.

`by cases` is represented as a checked coverage fact plus ordered branches:

```text
CaseSplit {
    coverage,
    branches: [{ assumption: LocalPremise, steps, exit }, ...],
}
```

The emitter proves coverage before opening any branch, uses `rcases` to bind
one recorded assumption per branch, and gives every branch a child proof scope.
An exit is either the requested conclusion or a structured pair of a fact and
its negation; the latter produces `False` and is eliminated to the branch goal.
The current coverage backend recognizes only a binary disjunction of logical
complements and checks it with classical excluded middle.

`by contra` is represented by the exact reverse assumption, its local steps,
and the final contradiction pair. For the current atomic-goal slice Lean opens
`Classical.byContradiction`, registers the reverse assumption by its retained
`FactId`, emits the nested statements, and derives `False` from the recorded
fact and negation. Negative atomic goals are handled by deriving the positive
reverse assumption inside the same classical scope.

The nearest boundaries remain explicit. Bare selection from meta-level
`set`, `nonempty_set`, or `finite_set` parameter types needs a separate
inhabited-type contract, and object carriers whose nonemptiness proof or object
IR has no backend remain incomplete. Existential extraction currently accepts
positive `exist`; `exist!`, `not exist`, preimage, function, piecewise,
recursive, tuple, sequence, and matrix forms remain separate boundaries. Other
`by` families need typed scope and exit contracts rather than reuse of the
case/contradiction nodes. Binder-owning goals and unsupported local statement
kinds also make the whole source statement incomplete transactionally.

The active implementation order is: native bound function spaces,
applications, and well-definedness certificates; then function-object
declaration/evaluation evidence; theorem/definition proof wrappers;
function-range preimage extraction; then induction, finite enumeration,
extension, and the remaining specialized `by` commands. Replacement preimages
need their analogous relation-witness package. This order keeps object
creation, temporary premises, and proof exits explicit before adding larger
proof families.

### Structured builtin-rule return path

The source-derived coverage ledger is
[`builtin_rule_inventory.md`](builtin_rule_inventory.md). Its generator follows
label arguments through forwarding helpers rather than counting only raw
constructors: 466 direct success-constructor calls currently expand to 659
label-bearing rule/strategy sites, including 558 distinct static labels. Each
row records its Rust source, family, checked Lean mapping, and delivery status;
evaluation/computation-like sites are classified separately. Forty-eight
source sites currently have a checked mapping. One generic source site
represents the 86 paired local RuleIds described below, so source-site and
catalog-entry counts are intentionally distinct.

Ordinary fixed-pattern local rules use a generated paired catalog. A rule has
exactly one restricted Litex `forall` schema under
`src/verify/local_builtin_catalog/<rule>.lit` and one checked Mathlib theorem
under `src/compile_to_lean/local_builtin_adapters/<rule>.lean`. Its path is the stable
`RuleId`; the generator freezes a semantic fingerprint and rejects missing or
duplicate pairs. The verifier uses a display-free structural matcher, binds
complete object subtrees, checks only already-known parameter requirements and
premises, and returns one generic `RegisteredLocal` certificate. Runtime
lowering rechecks the target, bindings, fingerprint, and child propositions;
the emitter links each required adapter exactly once and applies it in the
fixed binding/requirement/premise ABI. Adding another ordinary schema therefore
does not add another Rust evidence or IR enum variant.

Carrier information in that path remains occurrence-local. For example, the
certificate for `forall A, B set, x A` instantiates the type view of `x` with
the target occurrence of `A`; it does not attach types to every Litex object or
replace `Fact` with a complete typed Fact IR. Numerals likewise remain bare
objects, including signed canonical decimals; a judgment supplies a native
carrier expectation only when Lean needs one.

A diagnostic rule label is not a proof certificate. A compiler-supported
builtin therefore freezes its successful matcher bindings in
`BuiltinRuleEvidence` before the verifier stack unwinds. The enclosing
`VerifiedByBuiltinRuleResult` keeps that evidence beside the exact recursively
checked `StmtResult` subgoals. If the successful result is later merged into a
`VerifiedBys` sequence, both the evidence and subgoals move together.

Runtime lowering converts the semantic evidence to `LitexToLeanBuiltinRuleIr` and
recursively converts every subgoal to `LitexToLeanFactIr`. The result uses the same
general node as other derived proofs:

```text
RuleApplication {
    rule: Builtin(<typed rule application>),
    parameter_requirements: [...],
    premises: [<recursive child proof IR>, ...],
}
```

Registered local rules use the sibling `RegisteredRule` identity in the same
`RuleApplication` node. Legacy specialized evidence remains for reflection,
transforms, strategies, and rules not yet migrated to the paired catalog.

`BuiltinStrategy` remains the diagnostic identity of the search route. When a
successful structural decomposition exactly matches a supported arithmetic
contract, however, it now carries the same typed `BuiltinRuleEvidence` as a
direct rule. The current narrow bridge recognizes only exact additive
strict/weak premise shapes (`AddNonnegative`, `AddPositiveLeftStrict`, and
`AddPositiveRightStrict`). Any other strategy keeps its label and children but
has no compiler certificate, so strict compilation rejects it as
`OtherUnsupported` instead of inferring a tactic from the label.

Lean emission works back up that tree. It first materializes each child proof
inside the current proof scope, validates that the target and premise
propositions agree with the frozen bindings, and only then applies the Lean
lemma for the parent rule. Thus neither the runtime-to-IR layer nor the emitter
repeats Litex proof search.

This serialization does not widen verifier automation. The existing
`UseBuiltinRuleVerifyState` one-rule recursion budget still controls which
proof tree Litex may select; the compiler only preserves and checks that
already-selected tree.

Quotient nonzero illustrates the migration boundary. The direct
`a / b != 0` orientation is RuleId `nonzero.div`; its schema binds `a` and `b`,
retains both nonzero premises, and links the `div_ne_zero` adapter. The reversed
`0 != a / b` orientation still uses its earlier specialized evidence and
`Ne.symm`, because it is a distinct target schema. A resolved identifier that
merely denotes zero still verifies in Litex, but it has no compiler equality
transport for that resolution yet; it deliberately remains unsupported rather
than silently treating the identifier as literal zero.

Not-equality symmetry is the one-premise slice. The verifier records the
`NotEqualSymmetry` identity and returns the exact reversed non-equality as its
checked child. The emitter requires that child to be structurally opposite to
the target before applying `Ne.symm`; a changed citation or malformed child is
rejected instead of being guessed from the diagnostic label.

Subset/superset duality uses the same one-premise discipline. For example,
`A $subset B` proves `B $superset A`, and both propositions render as native
`A ⊆ B`. The verifier now retains the exact checked subset result instead of
returning a zero-child diagnostic. The emitter checks the polarity, direction,
and reversed operands before reusing that child. Reflexive and standard-set
duality routes that still return no child remain outside this MVP.

Closed `$prime(n)` and `not $prime(n)` computation carries a distinct
`PrimeU64Reflection` identity. The proposition lowers to `Nat.Prime n` or its
negation, the target is revalidated as one literal `u64`, and Lean checks the
result with `norm_num`. This is proof-producing reflection, not a default type
assigned to bare numerals and not an ordinary local-rule schema.

Closed `$coprime(a,b)` and its negation use the parallel
`CoprimeNaturalReflection` identity. Both argument occurrences are fixed to
`ℕ`, the proposition lowers to `Nat.Coprime a b`, and Lean checks the exact
gcd computation with `norm_num [Nat.Coprime]`. The reflection certificate
accepts natural literals only; it does not widen the Litex predicate to `ℤ`.

Equality-class lookup retains more than the final equivalent object: it now
returns an ordered path of original equality facts with an orientation for each
edge. A successful atomic-fact transport becomes an `EqualityRewrite` rule;
premise zero proves the source proposition and each following premise proves
the corresponding equality edge. The emitter first reconstructs those known
proofs, then normalizes the cited proposition and target through the recorded
equalities. A citation that changes its proposition without such structured
evidence becomes `OtherUnsupported` rather than an unchecked `exact`.

The equality store remains a compact proof forest rather than an all-pairs
closure or a shortest-path table. Redundant equalities, side branches, and
disconnected classes therefore do not become dependencies merely because they
were visible during verification. While the successful verifier scope is still
alive, it freezes the chosen oriented edges together with the source and edge
`FactId`s into `EqualityTransportEvidence`. Litex-to-Lean lowering consumes that
certificate directly; it does not search expired environments or identify an
edge again from printed text. An equality obtained only through a verifier
backend whose derivation is not represented in compiler IR is rejected at this
boundary instead of being emitted without proof provenance.

Atomic-fact resolution can combine that equality transport with computation.
The verifier searches from the requested proposition toward a stored fact, but
freezes the successful route in the opposite, proof-construction direction as
`FactTransformationEvidence { source, steps }`. Each step names its resulting
proposition and is currently either `RationalNormalization` or an
`EqualityRewrite` carrying the oriented equality edges and their stored
`FactId`s. This lets Litex-to-Lean reconstruct the cited source, replay a nested
normalization node, and finally rewrite to the exact goal. It never treats
`resolve_obj` itself as a Lean proof rule.

Resolution traverses the full object structure and substitutes named symbols
by `SymbolId`, so an equality for `a` can change an occurrence below both an
arithmetic node and a function application. For example, the retained route
for `$p(f(a + b), c)` is `$p(f(14), c)`, then `$p(f(13 + 1), c)`, then the
requested fact. The fast structural known-fact lookup records the same package
instead of bypassing the slower resolved-fact retry. General Litex function
objects still have no checked target object ABI; their recursive transformation
is retained and unit-tested, but Litex-to-Lean stops at that separate object boundary.

Equality transport itself is also recursive rather than limited to atomic
symbols. At every supported object node it first looks for a checked equality
path between the complete subobjects; if none exists, it descends through the
central same-shape matcher. Thus a stored `a + b = 14` replays
`$p(f(14), c) -> $p(f(a + b), c)` with the same oriented edge and `FactId`, at
any nesting depth covered by that matcher. This is equality congruence only:
normalization, definition reduction, and future computational transports keep
their own proof rules.

Known-forall evidence retains each parameter name, structural argument object,
parameter constraint, native target carrier, and recursively verified
requirement. A constraint such as `z Z` is emitted as the bounded binder
`z ∈ Litex.StandardSets.Z`: Lean unfolds that transparent alias to
`Set.univ : Set ℤ`, elaborates `z` at type `ℤ`, and keeps the membership as a
separate proposition and proof argument. The runtime also
instantiates the cited forall's selected conclusion with the recorded objects.
Consequently, `KnownForallInstantiation` proves that direct instance rather
than silently claiming the final goal. If the verifier matched objects that
are rationally equal but print differently, a separate outer `Normalization`
node records the move from the direct instance to the requested goal.
Statement memoization is a transparent proof wrapper and does not erase the
underlying route.

For forall introduction, temporary parameter facts are likewise retained with
their IDs. A generic `set` parameter becomes `Set α` under an implicit carrier
and needs no extra proposition; numeric and other domain memberships become
named local proofs.
Cached citations and known-forall requirements capture their source `FactId`
while the source environment is alive, so a temporary premise can remain a
local Lean proof argument after its Litex scope has been popped.

Typed consequences inferred in that same temporary environment are stored in
`ForallIntroduction.inferred_premises` with their original `FactId`s before the
scope closes. The first checked instance is `a ∈ R+ -> 0 < a`:
`PositiveRealMembership` cites the binder membership, validates the exact
object on both sides, and uses the definitional membership predicate of the
transparent `Litex.StandardSets.RPos` alias. No private real-value projection
is required.

## Lean surface

For a standalone file such as `chapter01-introduction.lit`, the generated Lean
surface begins with:

```lean
import Mathlib

namespace chapter01_introduction

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) :=
  ⟨True.intro⟩

namespace Litex.StandardSets

abbrev N : Set ℕ := Set.univ
abbrev NPos : Set ℕ := Set.Ioi 0
abbrev Z : Set ℤ := Set.univ
abbrev ZNeg : Set ℤ := Set.Iio 0
abbrev ZStar : Set ℤ := {z | z ≠ 0}
abbrev Q : Set ℚ := Set.univ
abbrev QPos : Set ℚ := Set.Ioi 0
abbrev QNeg : Set ℚ := Set.Iio 0
abbrev QStar : Set ℚ := {q | q ≠ 0}
abbrev R : Set ℝ := Set.univ
abbrev RPos : Set ℝ := Set.Ioi 0
abbrev RNeg : Set ℝ := Set.Iio 0
abbrev RStar : Set ℝ := {r | r ≠ 0}
abbrev C : Set ℂ := Set.univ
abbrev CStar : Set ℂ := {c | c ≠ 0}

end Litex.StandardSets

-- generated declarations

end

end chapter01_introduction
```

Generated proposition declarations use Lean's `Prop` directly; no fact wrapper
or alias is emitted. The object marker records the source invariant that
supported values are Litex objects; it is not a universal value wrapper.
Every generated file declares the complete current standard-set family once
under `Litex.StandardSets`. Standard-domain objects then render as transparent
names such as `Litex.StandardSets.R`, whose definition is Mathlib's native
`Set.univ : Set ℝ`. A numeral remains bare, as in
`2 ∈ Litex.StandardSets.R`, or in the unconstrained reflexivity `2 = 2`.
Compact standard subsets use the same native predicate sets behind stable
names: `R+`, `R-`, and `R*` become `RPos`, `RNeg`, and `RStar`. The
corresponding natural, integer, rational, and complex variants follow the same
rule; `Z+` is Litex's alias of `N+`, while the unordered `C+` spelling remains
invalid. These declarations are `abbrev`s, not typeclass instances or
subtypes, so membership stays an ordinary reducible proposition.
Closed numeric membership and nonmembership facts over these compact sets use
a fact-level carrier recorded by the verifier-to-IR bridge and emit a checked
`norm_num` proof. This carrier expectation applies to the whole judgment; it
does not annotate the source numeral or turn `trust` into type inference.
`trust` never fills in a missing numeric carrier, so an otherwise
underconstrained division judgment fails closed. When a fixed integer
expression is judged to belong to `Q`, the emitter gives the whole expression a rational expectation,
as in `(z / 2 : ℚ)`, so Lean inserts its canonical coercion without changing
the structural `LitexToLeanObjectIr` spelling.
Known membership in one standard numeric set may be projected through the
centralized Litex hierarchy by one structured certificate. Its single child is
the exact source membership, and the emitter validates the source set, target
set, object identity, and permitted relation before inserting any native Lean
coercion. This covers same-carrier refinement erasure and supported widening
through `N`, `Z`, `Q`, `R`, and `C`; it does not define the separate direct
proposition `N $subset Z`.

Builtin propositions keep their native logical shape. `A $superset B` is
`B ⊆ A`; positive proper subset is `(A ⊆ B) ∧ A ≠ B`; its Litex negation is
rendered by the verifier definition `¬ (A ⊆ B) ∨ A = B`. Proper superset
reverses only the containment. The four negated comparisons become native
negations of `<`, `≤`, `>`, and `≥`. `$prime(n)` alone fixes the
argument judgment to `ℕ` and becomes `Nat.Prime n`; it does not give an
intrinsic type to the numeral or symbol outside that occurrence.
Likewise, `$coprime(a,b)` fixes both argument occurrences to `ℕ` and becomes
`Nat.Coprime a b`.

The anonymous `noncomputable section` encloses both the shared prelude and all
generated declarations. In particular, polymorphic theorems remain in scope of
`universe u`; the anonymous section closes before the optional
named namespace. Synthetic generic carriers use Unicode `α` for the first
carrier and `α1`, `α2`, and so on when independent carriers remain in scope.
Homogeneous equality, not-equality, and set relations merge connected generic
carriers before binders are emitted.

The emitter never uses a fixed synthetic namespace such as `LitexGenerated`.
A registered file or module uses its canonical Litex name, with `::` mapped to
Lean's `.`, so `A::chap2` becomes `A.chap2`. A standalone runtime whose source
path ends in `.lit` falls back to the sanitized file stem. The canonical name
takes precedence over that fallback.

`compile_to_lean_from_source` remains anonymous and emits declarations at the file
root, even when its diagnostic label looks like a `.lit` path. The pure
`emit_lean_from_litex_to_lean_ir` boundary is likewise anonymous because IR intentionally
contains no source context. Callers compiling an actual file should use
`compile_to_lean` with that file's Runtime context.

This namespace selection scopes one emitted source. It does not add repository
traversal, Lean imports, or cross-file `FactId` lowering to the current MVP.

The current lowering is intentionally small:

- `abstract_prop` becomes a carrier-polymorphic `opaque` proposition over zero
  or more arguments with `LitexObject` constraints;
- a typed `prop` over the currently supported parameter surface becomes `def`
  (or `opaque` when it has no body), with standard-domain parameters using
  native Mathlib carriers and generic sets using `Set α`;
- only an explicit Litex `trust` becomes Lean `axiom`;
- stored proved facts become `theorem fact<FactId>`; for example, source fact
  `f4` becomes `fact4`; independently covered `forall` clauses become their
  exact runtime-stored projected theorems rather than one synthetic fact;
- a verified `thm name` becomes `theorem name`; its complete forall proof keeps
  the source parameter/domain scope and ordered proof steps, and a primary
  stored `FactId` resolves directly to `name` rather than producing a second
  synonymous `factN` declaration;
- explicit-value `have x T = e` becomes a checked `def` at file scope or a
  checked `let` inside a proof, followed by its stored type and equality facts;
- `by cases` proves its coverage, opens one scoped branch per recorded local
  premise, and checks either a conclusion or contradiction exit in each;
- atomic `by contra` uses the retained reverse premise and contradiction inside
  one `Classical.byContradiction` scope;
- known-forall application first materializes every chosen object at its
  retained native carrier as a `proof_arg_<SpaceId>_<LocalIndex>`, replays every domain requirement
  as a `proof_fact`, and names the direct instantiated conclusion before using
  it;
- definition evidence uses the named Lean definition;
- each generated proof block lazily receives a `SpaceId`; introduced premises
  and intermediate facts are named `proof_fact_<SpaceId>_<LocalIndex>`;
- `proof_arg` and `proof_fact` share one local index stream, so their coordinates
  preserve the actual derivation order inside a proof space;
- a nested proof block inherits visible outer facts; when it first introduces
  a named fact, it receives a fresh `SpaceId` and starts its `LocalIndex` at
  one;
- when a direct forall instance needs checked rational normalization to become
  the final goal, that application is emitted in a nested proof space and the
  outer proof names both the direct instance and normalized result;
- equality transport replays its source, equality edges, and result as
  consecutive `proof_fact` values, with the result checked by
  `simpa only [...] using ...`;
- quotient-nonzero builtin evidence replays its two recursively checked
  nonzero premises and applies `div_ne_zero`, with the recorded target
  orientation deciding whether `Ne.symm` is required;
- not-equality-symmetry evidence replays one exactly reversed non-equality
  premise and applies `Ne.symm` only after checking both orientations;
- subset/superset-duality evidence replays one exactly reversed containment
  premise and emits the same native `⊆` proposition;
- closed-u64 prime evidence emits native `Nat.Prime` and is checked by
  `norm_num` without emitting the inferred trial-division internals;
- closed natural coprime evidence emits native `Nat.Coprime` and is checked by
  `norm_num [Nat.Coprime]` without lowering through Litex's partial gcd object;
- arithmetic/order builtin evidence checks the target and ordered premise fact
  families, recursively materializes those premise proofs, and applies one of
  `linarith only`, `mul_nonneg`, `mul_pos`, `div_nonneg`, or `div_pos`;
- registered local evidence revalidates its RuleId and fingerprint, recursively
  materializes parameter requirements and premises, and applies the generated
  checked adapter without consulting a diagnostic label;
- verified rational-expression normalization operates directly on native
  terms and discharges them with `norm_num`, `ring`, or `field_simp` followed
  by `ring`;
- context-free object lowering preserves symbols, bare normalized numerals,
  standard sets, scalar applications, native bound function sets and exact
function-application layers, and the simple set constructors
  `union`, `intersect`, `set_minus`, `big_union`, `big_intersect`,
  `power_set`, and list sets;
- binder-owning `SetBuilder` retains its local symbol, base set, carrier, and
  ordered predicates, then lowers to one native predicate set;
- anonymous functions retain their own parameter scope and lower to native
  lambdas; membership in a refined function set replays the checked pointwise
  `forall` proof instead of trusting signature equality.

The native function ABI preserves a source `fn(...)` as a set over a dependent
Lean function carrier. A universal return set uses `Set.univ`; a refined return
set uses a set predicate requiring pointwise membership. Within each Litex
application layer all value arguments precede the layer's domain-proof
arguments; a nested returned function begins the next layer. This target
currying does not make additional Litex spellings legal. The verifier freezes
every successful WD proof into an environment-owned DAG. `WellDefinedObjProofId`
names object nodes and `WellDefinedFactId` names the exact factual proofs they
cite. A statement retains root IDs plus a frozen projection for later IR/report
lowering; it does not make those proofs ordinary Litex facts. Target-consumed
requirements are inserted as function arguments, while source-only obligations
are still emitted as checked audit facts. The emitter never substitutes
`by assumption` or reruns proof search for a missing certificate.

Certificate replay follows Litex's verification order. The complete WD result
for every relevant object occurrence is retained before the containing fact is
proved. Outer `forall` binders and their inferred parameter/domain facts enter
scope before dependent WD proofs are emitted; a binder belonging only to a
function signature is generalized in its helper, while a closed witness may
be emitted globally. Failed function-space candidates roll back their trial
evidence, and an evidence-free boolean object-cache hit cannot certify output.
Nested objects cite direct child proof IDs, so `f(g(h(x)))` is retained as a
DAG rather than a flattened bag of propositions.

WD visibility follows the ordinary Litex environment stack. A child can cite a
parent proof. Popping an uncommitted child discards its store and cache; only
nodes still referenced by an enclosing active capture are projected upward so
that the outer result can be frozen. Committing a child merges both its store
and its cache. Imported modules do not contribute reusable WD cache entries.
Cache identity is the object plus every callable contract actually used by its
AST. For a stored function membership that contract is the exact `FactId` that
installed the current `fn(...)` slot, so replacing a function's current return
contract cannot reuse a stale application proof.

Runtime-wide IDs are never recycled, but environment visibility remains the
authority for citation. Closed/file-scope proofs use deterministic Lean names
`well_defined_fact_<WellDefinedFactId>` and are emitted once. Scoped proofs use
`well_defined_fact_<proof-space>_<local-index>` and may be reused only inside
that Lean proof context. The recursion guard for an object currently under WD
checking is transient cycle control, not proof evidence.

The checked named-definition slice lowers a checked numeric-return
`have fn ... = ...` to a native dependent `def`, its membership theorem, and
the exact stored defining equality. Later evaluation is accepted only from a
structured verifier result that names that defining `FactId`, the application
side, the reduced side, and the checked orientation; Lean then checks the
reduction with `simpa only [name]`. For a refined return set such as `R+`, the
definition replays its checked body-membership proof under the same binders and
exports it as the function's pointwise membership theorem. Other richer
function-definition forms and untyped proof routes remain fail-closed.

Unsupported proof rules, propositions, objects, parameter types, composite
proofs, and inference origins stop strict compilation with an error. Report
mode instead marks the result `Incomplete`, rolls back and comments the omitted
statement, and continues. Neither mode falls back to `axiom` or `sorry`.

The MVP also requires every cited global `FactId` to have been emitted earlier
in the same IR stream. Facts preloaded during ordinary execution still have
stable IDs, but compiling them through an external Lean library mapping is a
future backend feature; an unresolved preloaded ID is rejected instead of
becoming an undefined Lean name.

## Example authoring ledger

Small self-contained compiler examples live together in
[`examples/09_compile_to_lean/compile_to_lean_examples.md`](../../examples/09_compile_to_lean/compile_to_lean_examples.md).
Each lowercase snake-case H2 section contains one self-contained `litex` fence
followed by its complete generated `lean` fence. The harness discovers every
pair automatically, verifies the Litex source, regenerates Lean, and rejects a
stale adjacent snapshot. Strict compilation is the default; an intentional
report-mode section carries `<!-- to-lean: partial -->` before its Litex fence.

Do not add another `.lit` for an ordinary mapping or proof-certificate example.
Standalone files remain appropriate for module/import order, CLI and path
behavior, or a durable runnable tracer whose acceptance contract requires real
file semantics.

```text
cargo test --release compile_to_lean_examples_markdown_emits_checked_source -- --nocapture
cargo test --release refresh_compile_to_lean_examples_markdown_snapshots -- --ignored --nocapture
```

## Active tracer

[`examples/05_compiler_interop/litex_to_lean_ir_mvp.lit`](../../examples/05_compiler_interop/litex_to_lean_ir_mvp.lit)
covers the full first vertical slice: abstract proposition, concrete
proposition, trusted forall, explicit known-forall arguments and requirements,
direct-instance-to-goal normalization, definition proof, temporary-premise
reuse, equality transport, forall introduction, and rational builtin proof.

[`examples/05_compiler_interop/compile_to_lean_resolved_atomic_fact.lit`](../../examples/05_compiler_interop/compile_to_lean_resolved_atomic_fact.lit)
is the recursive-resolution tracer. It records the verifier's goal-to-source
search as a source-to-goal `Normalization` followed by `EqualityRewrite`, with
both equality `FactId`s preserved. A focused nested-function regression proves
that the object walk descends through application arguments while retaining the
current explicit function-object ABI boundary.

[`examples/05_compiler_interop/compile_to_lean_function_well_definedness.lit`](../../examples/05_compiler_interop/compile_to_lean_function_well_definedness.lit)
is the native function and WD-certificate tracer. It covers closed and local
restricted applications, refined `R*`/`R+` binder proofs, source-only division
checks, flat versus nested application layers, native `SetBuilder` predicates,
anonymous lambdas, flat and nested refined output membership, a named
reciprocal definition, and a named refined-return definition. Object
occurrences retain all audited WD facts, while target-consumed function
requirements point to exact certificate IDs. Its commented cases record the
remaining wrong-layer, signature-switching, unsupported-constructor, and
untyped-proof boundaries.

[`examples/09_compile_to_lean/compile_to_lean_examples.md#environment_well_definedness_cache`](../../examples/09_compile_to_lean/compile_to_lean_examples.md#environment_well_definedness_cache)
is the environment-identity tracer. Two global statements apply the same
restricted named function; the second cites the first application's exact
environment-owned object/fact IDs, and the generated module declares the
closed domain helper once under its stable `WellDefinedFactId` name.

[`examples/05_compiler_interop/compile_to_lean_builtin_rule_ir.lit`](../../examples/05_compiler_interop/compile_to_lean_builtin_rule_ir.lit)
is the builtin-rule tracer. It follows one quotient-nonzero proof from matched
Litex arguments, through the generic RuleId/fingerprint certificate and
recursive subgoal results, to the paired checked `div_ne_zero` adapter. Focused
Rust regressions also cover the reversed legacy orientation, malformed arity,
unknown RuleId, stale fingerprint, and unresolved-zero-alias boundary.

[`examples/05_compiler_interop/compile_to_lean_local_builtin_catalog.lit`](../../examples/05_compiler_interop/compile_to_lean_local_builtin_catalog.lit)
is the full paired-catalog acceptance tracer. It exercises all 86 current
RuleIds, including dependent set-member carriers, elementary subset laws,
native set finiteness/nonemptiness, min/max lattice laws, nonzero
multiplication, strict-to-weak order, arithmetic sign/monotonicity rules,
and signed numerals; its complete generated module is
compiled by a real Mathlib/Lean kernel gate.

[`examples/01_proof_patterns/not_equal_symmetry.lit`](../../examples/01_proof_patterns/not_equal_symmetry.lit)
is the not-equality-symmetry tracer. It preserves the formerly rejected
Litex-to-Lean route, keeps `a != b` as the builtin child for `b != a`, and checks the
generated `Ne.symm` proof without adding an axiom or `sorry`.

[`examples/05_compiler_interop/compile_to_lean_builtin_rules_20.lit`](../../examples/05_compiler_interop/compile_to_lean_builtin_rules_20.lit)
is the representative 20-rule arithmetic migration tracer. It covers strict-to-weak order,
subtraction signs, addition signs and monotonicity, multiplication signs, and
division signs. A focused regression requires 20 distinct registered RuleIds,
rejects malformed registered premise arity, and sends the complete generated module
through the real Lean kernel.

[`examples/05_compiler_interop/compile_to_lean_recursive_strategy_ir.lit`](../../examples/05_compiler_interop/compile_to_lean_recursive_strategy_ir.lit)
is the recursive-strategy tracer. It preserves the exact nested derivation for
`(a + b) + (c + d) > 0`: typed strict addition at the root, direct positive
addition on the left, typed nonnegative addition on the right, and checked
strict-to-weak leaves citing the four `R+` consequences. The file records the
old label-only behavior, the active result, the non-additive unsupported
boundary, and the focused commands. A malformed root rule ID is rejected, and
the complete generated theorem passes a real Mathlib/Lean kernel gate.

[`examples/05_compiler_interop/compile_to_lean_partial_report.lit`](../../examples/05_compiler_interop/compile_to_lean_partial_report.lit)
is the completeness tracer. Its supported rational equalities surround one
verified but unsupported trigonometric rule. Report mode returns
`Incomplete`, identifies statement 2, emits statements 1 and 3, and produces
Lean accepted by the real kernel; strict mode still rejects the same unsupported
rule.

[`examples/05_compiler_interop/compile_to_lean_numeric_obj_abi.lit`](../../examples/05_compiler_interop/compile_to_lean_numeric_obj_abi.lit)
is the numeric-object semantic tracer. It fixes source-side membership facts,
uniform object spellings, structured integer closure, the intrinsic `ℤ`
contract and closed computation of `%`, refined `Z*` divisor evidence, and the
guarded natural-subtraction boundary.

[`examples/05_compiler_interop/compile_to_lean_set_obj_abi.lit`](../../examples/05_compiler_interop/compile_to_lean_set_obj_abi.lit)
is the implemented structural object tracer. It sends `union`, `intersect`,
and `set_minus` through `LitexToLeanObjectIr` to native `Set α` operations.
Binder-owned predicate sets are covered by the function/WD tracer and its
focused native-`SetBuilder` regression.

[`examples/05_compiler_interop/compile_to_lean_statement_scopes.lit`](../../examples/05_compiler_interop/compile_to_lean_statement_scopes.lit)
is the statement-scope tracer. It covers explicit-value `have`, local proof
steps in both branches and contradiction scope, case coverage, branch-local
assumptions, and reverse-assumption lifetime. Focused negative regressions keep
unsupported local statements explicit, and the generated scope proof is checked
by a real Mathlib/Lean kernel gate.

[`examples/05_compiler_interop/compile_to_lean_choice_have.lit`](../../examples/05_compiler_interop/compile_to_lean_choice_have.lit)
is the typed-choice tracer. It covers top-level and proof-local `have x R`,
later membership citation, the exact existential source certificate, and the
remaining meta-level parameter-type boundary. Focused malformed-IR regressions
remove or mismatch that evidence, and the generated choice declarations pass a
real Mathlib/Lean kernel gate.

[`examples/05_compiler_interop/compile_to_lean_exist_have.lit`](../../examples/05_compiler_interop/compile_to_lean_exist_have.lit)
is the existential tracer. It covers trust-free existential introduction,
explicit `obtain`, body-style `have`, proof-local extraction, alpha-renamed
citations, and ordered multi-witness packages. Malformed introduction and
projection evidence is rejected, and the complete generated file passes a real
Mathlib/Lean kernel gate.

[`examples/01_proof_patterns/witness_atomic_fact.lit`](../../examples/01_proof_patterns/witness_atomic_fact.lit)
is the named-introduction tracer. It proves an integer divisibility prop from a
concrete witness, cites the named fact, projects the existential again through
`obtain`, and passes malformed-IR plus real Mathlib kernel gates.

Rust and Litex gates:

```text
cargo test --release compile_to_lean:: -- --nocapture
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/litex_to_lean_ir_mvp.lit
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_resolved_atomic_fact.lit
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_builtin_rules_20.lit
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_recursive_strategy_ir.lit
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_set_obj_abi.lit
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_function_well_definedness.lit
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_statement_scopes.lit
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_choice_have.lit
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_exist_have.lit
```

Actual Lean-kernel gate (requires an already-fetched Mathlib Lake project):

```text
LITEX_LEAN_PROJECT=/path/to/mathlib-project \
LITEX_LAKE=/optional/absolute/path/to/lake \
  cargo test --release compile_to_lean_mvp_compiles_with_lean -- --ignored --nocapture
LITEX_LEAN_PROJECT=/path/to/mathlib-project \
LITEX_LAKE=/optional/absolute/path/to/lake \
  cargo test --release compile_to_lean_builtin_rules_20_compiles_with_lean -- --ignored --nocapture
LITEX_LEAN_PROJECT=/path/to/mathlib-project \
LITEX_LAKE=/optional/absolute/path/to/lake \
  cargo test --release compile_to_lean_recursive_strategy_ir_compiles_with_lean -- --ignored --nocapture
LITEX_LEAN_PROJECT=/path/to/mathlib-project \
LITEX_LAKE=/optional/absolute/path/to/lake \
  cargo test --release generated_restricted_function_well_definedness_compiles_with_lean -- --ignored --nocapture
LITEX_LEAN=/absolute/path/to/lean \
  cargo test --release compile_to_lean_set_obj_abi_compiles_with_lean_core -- --ignored --nocapture
LITEX_LEAN=/absolute/path/to/lean \
  cargo test --release compile_to_lean_statement_scopes_compile_with_lean_core -- --ignored --nocapture
LITEX_LEAN=/absolute/path/to/lean \
  cargo test --release compile_to_lean_choice_have_compiles_with_lean_core -- --ignored --nocapture
LITEX_LEAN=/absolute/path/to/lean \
  cargo test --release compile_to_lean_exist_have_compiles_with_lean_core -- --ignored --nocapture
```

For scratch work, these commands first verify `examples/tmp.lit`,
`examples/tmp1.lit`, or `examples/tmp2.lit`, generate the corresponding Lean
translation, and append it to that file inside a triple-quoted Litex comment.
Each successful command also replaces
`/Users/shenjiachen/主要文件夹/GeekGems/2026/mathematics_in_lean/tmp.lean`
with the generated Lean source, so the destination never retains content from
the previous run. Set `LITEX_TMP_LEAN_PATH` to use a different destination.
`tmp2.lit` is also the equality-path gallery, including clean, reversed,
redundant, branched, disconnected, repeated-argument, and independent paths.

```text
cargo test --release compile_tmp0_to_lean -- --nocapture
cargo test --release compile_tmp1_to_lean -- --nocapture
cargo test --release compile_tmp2_to_lean -- --nocapture
```

The source file is left unchanged when verification or Lean generation fails.
Before writing a successful snapshot, the command removes the last
triple-quoted block when that block is at the end of the file. Triple-quoted
blocks elsewhere in the source are preserved.

Implementation lives in `src/litex_to_lean_ir`,
`src/runtime/runtime_litex_to_lean_ir.rs`, and `src/compile_to_lean`.
