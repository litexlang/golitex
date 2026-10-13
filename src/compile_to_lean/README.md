# Litex-to-Lean Compiler Implementation

This module compiles the completed typed execution result into Lean source.
The [compiler guide](../../docs/Litex_To_Lean_Compiler_Guide.md) explains source
semantics and examples; [CLI documentation](../../docs/cli.md#lean-compiler-boundary)
owns invocation and output behavior.

## Public entrypoint

```rust
let result = runtime.run_litex_code(&source)?;
let compiler = LitexToLeanCompiler::new(runtime);
let lean = compiler.compile_run(&result, &namespace)?;
```

The compiler owns only the original `Runtime`, moved into it after source
execution without cloning. It has no lifetime parameter or result field.
`compile_run(&self, result, namespace)` receives the completed run as a method
input and reads Runtime only for exact citation resolution. Branch methods
likewise receive their original typed results as parameters. Reusing the same
compiler does not retain an earlier result or partial output.

The free `compile_run(result, runtime, namespace)` convenience function also
takes ownership of Runtime; its previous borrowed-Runtime signature has changed.
The CLI executes source once, transfers Runtime into the compiler, and returns
the complete artifact only after every statement is compiled.

## Result dispatch and file ownership

The layout mirrors `src/execute`: one dispatcher per existing result enum and
separate files/folders for its mathematical branches. Methods belong to the
same `LitexToLeanCompiler`; there are no mutable child compilers or parallel
compiler result types.

```text
RunLitexCodeResult.statement_results
  -> ExecStmtResult
     -> ExecDefinitionStmtResult
        -> DefineObj / DefProp / HaveFnEqual / HaveFnByInduc / DefThm
     -> ExecByStmtResult -> ByThm / Induc
     -> ExecReleaseAndExpandStmtResult -> ReleaseThm
     -> ExecProofBlockStmtResult -> Claim -> forall / non-forall body
     -> ExecFactStmtResult -> VerifyFactResult
        -> equality / atomic-except-equality / forall / And / chain / Or
        -> selected searched_proof and its original children
        -> object WD and its original constructor/domain evidence
```

The entrypoint owns run validation, namespace/header output and ordered traversal.
Statement dispatch belongs to `compile_stmt_result`; leaf owners mirror let,
have, function, theorem, invocation, induction and fact-result branches.
`source_position` reads the original result prefix/ancestors;
`source_queries` resolves exact subjects.
`compile_store_result` validates actual stores. Naming helpers spell existing source IDs;
`lean_compile_error` reports source statement position and rejected route.

## Borrow the source tree; generate temporary output

No persistent ObjectTerm, NumericTerm, FactTerm, NamedTheorem, OutputReference,
EmittedFact, ContextParameter or output-scope registry is needed. Original
parameters, facts, stores and selected proofs remain in the source results.
Children return temporary Lean expressions; a proof renderer can return a
proposition and proof string without copying the source fact.

A source-position cursor contains only borrowed original result owners, parent
positions and the current stage/child boundary. It identifies which source
prefix is being compiled. For example, left-operand WD can be available before
right-operand cached WD, while the statement's truth proof is still unavailable.
It is neither another ExecEnv nor an object/fact/proof cache.
Its internal borrow lifetime remains explicit where Rust requires it; this
does not impose a lifetime parameter on the owning compiler API.

Inference replay reads the canonical `InferResult` tree and its atomic-family
rule enums. `OrderBoundInference<'a>` is a borrowed view of a strict-bound or
weak-integer leaf, used only by the source cursor; it owns no copied result or
new registry. The cursor exposes completed producers only for reviewed Lean
adapters, rather than treating every inferred store as a Lean hypothesis.

Each source proof is named `h_<original FactId>`, including exported facts,
named theorems, local hypotheses, stored alias equalities, supported inference
and theorem-return projections. Declarations and citations use the same actual
ID; statement positions determine traversal order, not proof names. Producers
are emitted at their actual stage. Temporary Verify children are not
automatically stored facts; some obligations reuse the owning target FactId.
Their selected proofs may be passed directly to certified constructors.

A declaration's parameters come from its original source position. Introducing
another object later cannot extend an earlier theorem's signature. Generic
hosts retain their own universe, Representation, certified Obj and ordinary
membership hypothesis. Universes and parameter strings are rendered from
source records, not retained in parallel compiler lists.

Some constructor types refer to an earlier local membership or domain proof.
When that proof name occurs in an exported proposition, close the proposition
over the necessary actual producer definitions as ordered Lean `let` values.
These are proof expressions, not additional assumptions. Unused definitions
are omitted, and the ordinary theorem statement remains definitionally equal
to the source proposition.

## Exact citation and scope checks

Lookup reads earlier siblings and active source ancestors. At root, earlier
exported statements are visible; their closed theorem/forall/call bodies are
not. In a local result, only introductions, assumptions and completed stages
are visible. Future siblings and later stages are unavailable.

Captured `local_env` and Runtime resolve exact FactId/WdId subjects only. A
resolved subject is insufficient: a supported source producer must also occur
in the visible original prefix. This preserves rejection of removed producers,
future references, wrong subjects and closed-scope citations even if Runtime
still holds a matching record. Unsupported inferred facts never become new
hypotheses.

Current results are not a standalone citation closure. Let retains stored IDs
rather than the full store/infer result, and anonymous ByDef WD does not retain
its later cache-registration ID. Root references also use live Runtime. Any
Runtime-free compilation requires an explicit producer-capture design; it must
not be simulated with a new compiler-owned store.

## Mathematical adapters and support boundary

Every object owns WD. Constructor compilation replays certified children and
exact membership/nonzero/domain proofs before truth evidence. Arithmetic keeps
Litex construction shape. Membership adds knowledge without choosing a new
host type for a generic object.

Numeric denotation, C/R-membership and closed-value evidence are rendered by
leaf helpers from actual source constructions and selected proofs. Removing a
numeric cache does not remove these semantic bridges or authorize recovering
a proof by target-shape matching.

Selected adapters include reflexivity, exact closed calculations, recorded
rational normalization, scalar division relations, arithmetic congruence,
equality paths, membership transport, supported numeric hierarchy and real
order routes. The selected `DiffNonzeroFromInequality` rule consumes its exact
ordered operand-inequality child and the subtraction's numeric domain evidence.
`Litex.subNonzeroOfNotSame` proves the common replay law; both zero orientations
retain the source endpoint's certified denotation. The
`nonzero_real_difference` pair exercises `x != 1 => x - 1 != 0`.
`DivNonzeroFromFactors` consumes the two recorded nonzero proofs in numerator /
denominator order, and known nonzero differences replay their exact citation
to prove operand inequality. The `real_mobius_involution` pair combines these
routes with nested guarded calls.
Fixed `ring`/guarded normalization checks the source-selected
certificate family; no independent target theorem search is performed. The
source Rational tag does not contain a monomial trace, so Lean checks the
normalization proof rather than replaying an unavailable low-level trace.
An original one/two-argument function call can be an opaque scalar leaf in
that normalization domain when its captured call WD and numeric return
observation are supported. Its arguments and guards remain obligations of
the original call WD; normalization does not search for their proofs.

Real absolute value retains `Litex.AbsObj`: its constructor consumes the
original argument WD and exact R-membership proof. Numeric observations use
the proved real denotation bridge; selected nonnegativity, nonnegative-argument
equality and even-power identities replay their own certificates. Absolute
value in a formula body uses the same semantic operation. Natural exponents
use the original N-membership to obtain a proof-independent native `ℕ`
observation without changing the source object. This supports composed powers
such as `(1 / 4)^(2^n)` and the selected product-of-powers and power-of-power
rules with their exact ordered base/exponent evidence.

`FnApplicationUnfoldSubstitution` equality evidence replays the exact
head-to-anonymous-function citation, original and selected call WD, binder-ID
beta substitution, scalar congruence and actual residual. Steps are consumed
once in original-tree order; inserted bodies and call arguments cannot acquire
extra expansions. Unsupported constructors and residuals reject the complete
artifact. Tests live under `tests/unit/compile_to_lean/fn_application_unfold_substitution/`.
Natural-function declarations retain the named signed-membership inference.
Its zero object is constructed by `Litex.number`, and `naturalNonnegative`
proves the conclusion from the original N-membership certificate. There is no
repeated Rust WD stage for the derived fact. The selected `ArithmeticCongruence` strategy
validates its exact ordered requirement facts and IDs, then compiles each child
at its original sibling position.
Structural membership includes N addition/multiplication and Z
addition/subtraction/multiplication/negation, plus closed nonnegative integer
powers in N/Z. The original base, exponent and carrier evidence is checked.
Natural subtraction and integer division do not acquire false closure laws.

The compiler also supports the phase-3 slice: top-level concrete predicates
with flat atomic defining clauses, and formula functions with one or two fixed
N/Z/Q/R/C inputs and output. Functions retain owned graph representations;
calls consume the recorded function membership, input memberships and atomic
guards. The additional `FunctionSemantics M` interface has a proved ZF model
in the same `lean/Litex.lean`. Its body callbacks interpret source objects,
without replacing their representations with native real arrows.

The Newton stage-1 extension adds `R+` inputs and targets to this one/two-input
formula slice. `RPos` is the derived separation of `R` by positivity. Input
memberships supply the base-real and positive-guard certificates; target APIs
use the actual semantic set with its sethood proof. Existing numeric APIs keep
their standard-set arguments. Signature and formula construction consume the
original completed return-set WD stage, including when the function is the
first source statement. Other signed targets remain unsupported.

`compile_claim_stmt_result` consumes successful claim results directly. The
owning producer retains its original statement, goal WD, introduced parameters,
assumed domains, proof steps, conclusion proofs, local environment and stored
goal. Its JSON projections retain their existing presentation fields. Helper
facts stay inside the claim; only the actually stored conclusion is exported.
Positive sum/quotient adapters consume the selected rules and their ordered
requirements, with original operation WD. The maintained tracer is
`lean/examples/newton_positive_update/statement.lit`.

Recursive declarations currently accept one N parameter, that parameter as the
measure, literal lower bound zero, no authored domain clauses, and the two
ordered leaf cases `n = 0` and `n > 0`. The base body cannot call itself;
successor self calls must use the exact source argument `n - 1`. Returns use
the supported N/Z/Q/R/C/R+ carriers and bodies use reviewed constructors.
The producer
retains its existing binder introduction, measure/lower WD, restricted self
membership store, case checks and final stores. The compiler emits an owned
`Litex.RecursiveNatFn` graph. `Nat.rec` interprets its histories internally;
each checked body uses the exact restricted prefix graph and its recorded
N-membership, smaller-index and lower-bound proofs. The declaration rule's
generated self signature is consumed from its actual store and earlier
signature formation, without inventing another verifier WD stage. Final case
equations preserve their stored FactIds. Unfolding replays the captured
selected guard path, original call WD and residual equality. Ordinary
single-group one/two-argument call congruence likewise consumes the original
ordered argument proofs followed by the function-head proof.

Ordinary `by induc k from 0` supports nonempty atomic or flat And/chain goals
whose constructors and proof routes are supported. Its checked integer
parameter, lower-domain WD/store, goal WD and separate base/step scopes remain
in the original result. The consumer replays each case's own introduction,
ordered assumptions, steps and goal proofs, then applies the proved integer
induction bridge to the source semantic predicate. Only the final stored
forall is exported. A local result quantifies over `M.Value` with the original
integer-membership and lower-bound premises. Its exact FactId citation adds
an anonymous Representation bridge from the caller's certified generic Obj
to its denotation; the caller universe is inferred at each use. Global exports
keep generic Obj binders, and no universe registry is introduced.
Its constructor factory uses the original goal header;
closed case facts remain unavailable. Strong induction, other lower bounds,
general recursion measures, nested cases and authored recursive domains retain
explicit rejection branches.

The full Newton source is
`lean/examples/newton_residual_bound/statement.lit`. Its all-index residual
proof passed strict verification and whole-file compilation. Complete generated
Lean checking and native all-index bound acceptance remain pending; successful
smaller-prefix checks do not establish those gates.
The final 2026-10-13 regression gates passed 429 compiler tests and 78 separate
JSON tests. Selected induction, theorem-result capture and by-thm selection
filters also passed; their overlapping tests are not counted as another total.

The phase-4 set slice preserves arbitrary `have A set` and set-kind universal
binders as generic certified parameters. Empty and finite enumerations retain
heterogeneous child objects and every actual pairwise inequality. The generated
insertion constructors consume those proofs rather than silently deduplicating
source values. Bounded builders retain their certified bound, exact binder
store, and ordered predicate WD/store stages. Earlier filters become proof
witnesses in later filter types; formation does not assert filter truth.

`SetSemantics M` supplies reviewed empty/insertion/separation/extensionality
laws. `FunctionSemantics M` extends the same set interface, so builder bounds
and function domains share separation. The actual ZF model proves every law
in `lean/Litex.lean`. Selected finite membership/subset, builder membership,
subset-definition and empty-domain universal routes replay their recorded
children. Builder inference retains its actual selected builder, exact equality
path and each direct conclusion store. Builder projections also retain whether
they came from the base carrier or the exact zero-based source condition index.
Replay validates that selected source against the stored subject; it does not
rediscover an index by searching for a matching conclusion. Proved Lean constructors establish the
objects used by the selected named rule. Missing, changed or
future producers reject instead of being recovered from the final environment.

Numeric `Set` views are pullbacks. A full real/complex-set interpretation also
requires the corresponding source subset witness. Native Adapter/Final checks
consume the generated set proofs through proved denotation/membership bridges.

Earlier one/two-input formula calls may occur in a formula body. Concrete
predicate guards and numeric RHS/let aliases replay their original definitions;
flat And/chain clauses keep ordered WD, stores and original component IDs.
Bounded builders accept these supported flat filters and their actual member
projections. KnownSubset consumes both its recorded member and subset citation.
The generated pairs include composed_real_formula, chain_guard_reciprocal,
closed_unit_interval and subset_real_membership_order.

Higher-order bodies, recursion outside the bounded slice above, nonempty/finite
binder kinds, local prop/function or nested theorem definitions, compound logic
outside the reviewed flat routes, unreviewed consumed
inference and module compilation retain explicit unsupported branches.
Exact certificates, orientations, argument
match evidence and residual children must be preserved. Generated files keep
all source proof names; only unused-variable and unused-section-variable
style linters are disabled. Real Lean checking and other warnings remain
separate required gates.

A theorem invocation retains `selected_wd`, the caller's existing formation
check after the invocation scope closes and before its selected fact is stored.
The original direct nested call now uses that caller evidence. A compound
constructor recorded only inside the closed invocation remains unavailable in
the parent. The existing closed-leaf traversal permits numeric literals and
standard sets; it does not export local binders, truth or general construction WD.

Consumed additive, subtractive, nonzero-factor, common-denominator and nonzero-
numerator cancellation retain their original membership/nonzero checks and the
rule-certified direct store. The compiler dispatches the original rule variant
to a proved cancellation lemma, emits its actual derived FactId without recursively
replaying another infer stage. Pending stages cannot cite their future conclusions,
even when an ancestor sees the completed store. Unreviewed inference families
retain explicit rejection branches.

`PositiveRealPower` equality inference retains the exact seed FactId, one or
two ordered equality-side transports, original selected base/power positivity,
exponent R-membership and direct R+ store. Each child is replayed at its source
stage and emitted as a checked local proof under its original FactId. Even when
the original natural/integer constructor WD already implies the exponent's
real membership, Lean checks that captured child. The power and opposite side
use the original equality WD, and only completed transport stores become
visible. The consumer never reconstructs a power WD from its inferred store.

Named theorem bodies accept the original by-def result alongside existing fact,
let, typed-have and by-thm steps. The source request must match its selected
definition proof subject. Completed by-def exposes the caller's goal WD;
constructors inside its closed defining-clause proof remain local. Ordinary
local arbitrary-have declarations now eliminate the captured nonempty numeric
carrier inside the proof. Set-kind local declarations use a certified semantic
set witness; only the original IsSet fact is published. Dependent typed-have
and let retain their own IDs. The exported theorem is rendered from the original
goal, so local witnesses and membership proofs do not become outer parameters.

Flat And/chains replay verification, actual storage projections, independent
inference seed IDs and numeric transitive closures in order. Conditional
integer-lower-bound and strict-positive rules retain their actual input
certificates and direct storage. A derived And/Chain still publishes its actual indexed
components, without inventing a nested infer stage. Pending rule/store positions
continue to reject their future producers.

`compile_known_application.rs` consumes the shared selected forall-application
certificate for supported atomic equality/non-equality, flat Chain/And and Or
conclusions. Equality through symmetry validates the captured reversed subject
before applying the same certificate and equality symmetry.
It validates the exact direct conclusion, argument matches, parameter-type
requirements and ordered domain proofs. Existing scoped formation and callee
instances remain the only constructor sources. Identifier-headed one/two-input
calls retain their captured argument slots and final function-prefix slot;
semantic call/pair congruence transports that recorded equality. Curried,
anonymous-head and unreviewed constructors remain rejected. This adds no
Runtime search, result fields, persistent registry or replacement proof.

Or replay supports a proved selected branch without assumed negated branches,
the captured integer successor-tail rule, and exact known-forall applications.
Branch formation, selection index, ordered integer/bound proofs and source
subjects are checked. Other disjunction strategies remain rejected.

Explicit by-thm calls also replay flat And/Chain returned packages. Original
domain proofs are followed by their captured `dom_stores`; all conclusion WD
finishes before any return package is published. Direct component selection
uses the package's actual stored FactIds, preserving the invocation's strict
selection contract. Caller `selected_wd` remains separate from the closed
invocation. `named_compound_theorem_returns` includes two scalar wrappers whose
final proofs genuinely cite the selected invocation stores.

`release thm` consumes the same user-theorem invocation stages and publishes
each supported scalar/flat And/chain return through its original caller
WD/store pair. All invocation-local conclusion WD finishes before export;
later returns can use only completed caller stages. Released stores and their
supported inference keep their actual FactIds. Qualified/builtin theorem
callees and other release families remain unsupported.

Concrete predicate equality transport uses the exact previous declaration,
predicate identity, polarity and arity, with ordered source equality proofs.
The declaration's raw predicate acts on semantic denotations. `congrArg` and
`Eq.mp` transport the original cited proof; generic host types remain intact.
`concrete_predicate_equality_transport` uses the transported fact as a real
function-domain guard, rather than unfolding a replacement proof.

Natural membership inference is published once per captured seed. Ordinary
parameter introductions keep their direct sign results. Predicate and builder
projections have named-rule evidence and direct stores; they do not contain
another infer stage.
A later explicit source membership can be a new seed with its own recorded
inference. Paired projection consumers replay the actual stored components. Completed
parameter inference supplies certified Lean primitive constructors to later
predicate and builder clauses. Completion labels and exact Atomic/Prop owner aliases preserve
nearest pending-stage limits; first-sign WD cannot cite its own future truth.
The natural_polynomial_formulas pair includes a concrete natural-output prop.

The original phases 8-11 minimum was accepted again on current single-hop
typed results on 2026-10-12. The coherent checkpoint checks 74 actual
source/generated pairs, 45 maintained profiles, six separate whole-known
Chain/And and WD-factory profiles, the original S01-S18/I01 matrix and 19
mathematical cross-cases. That checkpoint passed 311 compiler tests, pinned real
Lean, 64 exports per native layer and an ordinary Lake client with 64 direct
applications and six combinations. All 64 Final signatures remain unchanged;
the original 45 elaborated native statements match their phase-7 baseline.
The local completion matrix separates whole-file checks, selected
original result stages and actual native signatures. Ten new native interfaces
are closed evaluations, six are generic and three mix both scopes. Handwritten
adapters choose the proved model explicitly; this is not automatic native
interface generation or support for every Litex evidence variant. Receipts for
that checkpoint are acceptance_phase8_current through acceptance_phase11_current and
acceptance_phases8_11_current in the local-only compiler workspace. The
2026-10-11 phases 8-12 receipts remain historical evidence of their own build.

Any failed source, unsupported branch or unavailable evidence rejects the
entire artifact. No partial Lean file, new axiom, proof hole or fabricated
premise is emitted.

## Verification

```sh
cargo test --release --lib compile_to_lean::tests
python3 scripts/litex_to_lean/check.py
```

Rust tests check actual result contracts and corrupt/deleted producer controls.
The local gate separately runs strict source verification, actual CLI generation,
byte-for-byte pair drift, pinned Lean warnings-as-errors, negative controls and
native consumers. Canonical pairs belong in `lean/examples`; all check tooling,
receipts, Lake/dependencies, native adapters and drafts stay in ignored
`scripts/litex_to_lean`. Generated Lean files are changed only through the CLI.
