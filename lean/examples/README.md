# Compiler examples

This directory is the canonical generated example record for sources targeting the
`stmt_result_to_lean_compiler` ABI. Every example has one authoritative `.lit`
source and one same-name generated `.lean` output. It must not import or depend
on the archived universal-`Litex.Object` ABI.

Every generated file imports the public `Litex` umbrella module. The umbrella
owns the internal module list, so adding supported theorem or strategy modules
does not require changing the generated import header.

Refresh every pair from fresh Litex verification and verifier-owned recursive
Results:

```sh
cd lean
./stmt_result_to_lean_compiler.sh generate examples
```

After editing one source, refresh only its same-name output:

```sh
cd lean
./stmt_result_to_lean_compiler.sh compile examples/1_SetSystem.lit
```

Check byte-for-byte freshness and run every output through Lean:

```sh
cd lean
./stmt_result_to_lean_compiler.sh check examples
```

Compiler preserves source sketch scope. A top-level `sketch:` becomes an
isolated `__SketchNN` namespace nested inside the file namespace; declarations
and FactIds created there do not become later file-level bindings. Ordinary
top-level facts are emitted directly in the file namespace.

`37_TrustedObjectResultComposition.lit` covers parameter-only and
fact-attached `trust have` statements over ordinary object carriers. Each
binding becomes an explicit Lean axiom because the source statement itself is
an explicit trust boundary; its membership and attached fact keep the exact
Runtime-assigned FactIds. A later function application checks that the
compiler environment retained the callable contract and WD return-membership
edge without searching propositions.

`38_FactTransformationResultComposition.lit` covers a known-fact citation
followed by an ordered rational-normalization transformation. The compiler
starts from the exact cited FactId, validates the retained source/result of
each step, and emits a Lean `convert`; removing the step makes compilation fail
closed instead of silently reproving the target.

`39_CheckedNamedFunctionReductionResultComposition.lit` covers one checked
named-function unfolding. Its equality Result retains the defining equality's
exact FactId, the selected application side, and the reduced object. The
compiler resolves that FactId in its own environment stack and unfolds only
the recorded function; changing the FactId or reduced object fails before Lean
source is emitted.

`59_TransparentLetResolution.lit` covers one executed `let` used as a
callable alias. The verifier's transformation records the exact defining
equality `FactId` and one-pass `SymbolId` substitution; the compiler validates
both and unfolds only the recorded Lean definition. Ordinary proved
equalities remain outside this definition-reduction path.

`40_RegisteredOrderResultComposition.lit` covers the six registered additive
order rules. Each enclosing forall Result owns the parameter and premise
scope; the compiler environment stack makes those exact FactIds visible only
while compiling its conclusion. The arithmetic proof method then validates
the retained typed rule variant, stable rule ID, target operands, and ordered
child Results before applying one fixed `Litex.Rules` theorem. Swapped children
or mismatched typed evidence fail closed instead of falling back to rule-name
or label matching.

`41_ClearOrdinaryName.lit` covers the removal of the former environment
command. `clear` now follows the ordinary object-definition and fact paths in
both Litex and Lean compilation; a bare line does not reset either environment.

Order transitivity remains a typed verifier Result with the exact two-edge
path in child order, but it was not in the former local-builtin catalog and is
therefore not a positive compiler example. ToLean rejects it with the stable
ID `order.transitivity`; focused Rust contracts also reject reversed children.

`1_SetSystem.lit` is the tracer for checked named set aliases, `Same`, and
heterogeneous `In`: `have A set = R` becomes an `abbrev A : Litex.Set`, while
verifier equality-rewrite evidence becomes a `Litex.In.congr` proof. A bare
`have A set` remains outside this slice because the verifier has no checked
inhabited-type backend for that arbitrary choice.

`2_OrderSystem.lit` is the tracer for heterogeneous `Lt`/`Le`. Compiler emits
`Litex.Lt.toLe` only after validating the registered rule ID, fingerprint,
parameter evidence, and premise evidence.

`3_AtomicEquality.lit` is the first tracer with ordinary top-level facts rather
than a `sketch`. It maps numeric equality to `Litex.Same`, consumes
`ObjectReflexivity` or checked rational-normalization proof IR, and replays the
captured closed-numeric WD membership facts inside the generated theorem.

`4_FunctionSet.lit` is the first unary function-set tracer. Set parameters are
emitted as `Litex.Set` values, while `x` and `f` retain independent carriers
and explicit `Litex.In` hypotheses. Every generated `Litex.fnApply` consumes
the verifier-selected function-membership FactId proof and argument-membership
WD proof. The source `forall` is deliberately top-level rather than wrapped in
`sketch`, so its generated theorem is also file-level. Anonymous functions,
multiple arguments, domain clauses, and curried returns remain outside this
first adapter.

`5_AtomicMembership.lit` covers ordinary top-level membership in the standard
numeric sets. Numerals remain complex-valued Lean terms, while the generated
theorems construct separate `Litex.In` evidence for `N`, `Z`, `Q`, `R`, and
`C`; Lean typing never substitutes for Litex membership.

`6_FactReplay.lit` covers exact verifier-owned proof reuse. Equality symmetry
and transitivity replay cited FactIds through `Litex.Same`, negated equality
uses its proved symmetry rule, and an alpha-equivalent universal statement
cites the previously emitted forall theorem.

`7_PropositionalFacts.lit` covers conjunction and disjunction introduction as
well as structural conjunction projection. A projected local fact is emitted
only when its exact FactId is cited by a conclusion.

`8_ProofScopes.lit` covers source-named `thm` declarations plus local `claim`
and `example` blocks. Local facts remain Lean `have`s and are resolved only by
their verifier-owned FactIds.

`9_CasesAndContradiction.lit` covers `by cases` and `by contra`. Branch facts
and reverse assumptions are installed in cloned contexts, so neither can leak
outside its source scope.

`10_ExistentialWitness.lit` covers one positive witness and one body fact. A
witness over a user set retains an independent Lean carrier and an explicit
`Litex.In`; the standard-real elimination tracer chooses a native `ℂ` witness
and projects the exact membership and body roles.

`11_ObjectDefinitions.lit` covers the minimum native definition layer:
untyped `let` and one membership-constrained `have ... = ...`. Definitions use
ordinary Lean values, while their stored Litex membership and `Same` facts are
replayed from verifier evidence.

`12_NamedFunction.lit` closes the first function construction/application
loop. The identity and `inc(x)=x+1` definitions become native `Litex.Fn`
values. `reciprocal(x: x != 0)=1/x` becomes `Litex.FnWhere`; its call
consumes the verifier-selected function membership, argument membership, and
nonzero domain FactId. Checked reductions use the closed real/complex
operation congruence routes.

`13_PredicateDefinitions.lit` covers concrete `prop` plus `by def`. The Lean
definition includes parameter-membership requirements and defining clauses;
reduction and the inferred projections preserve their checked component
order. Abstract or bodyless predicates remain fail-closed.

`14_SetBuilderAndChoice.lit` covers an exact subtype carrier, non-reflexive
`x = 1` membership, one-parameter concrete-predicate transport, the base and
predicate projection adapters, and choice from a set whose nonemptiness proof
was retained by the verifier. It never uses `Set.univ` or a universal object
carrier.

`15_BuiltinStrategy.lit` traces recursive additive-sign search. Each selected
strategy layer remains visible as `UseBuiltinStrategy` in IR, while its inner
tree records the exact arithmetic rule and cited FactIds. Lean emission unwraps
only that marker and calls reviewed rules; it never re-runs strategy search.

`16_StandardSetHierarchy.lit` traces all ten proper projections in the base
numeric hierarchy `N → Z → Q → R → C`. Generated proofs compose four proved
adjacent membership bridges and retain each complex-valued binder's original
`Litex.In` premise. Refined carriers are represented separately rather than
being collapsed into this base hierarchy.

`17_NumericCarrierClosures.lit` traces complex `+`, `-`, `*`, `/` closure and
integer `+`, `-`, `*`, `%` closure. The modulo theorem makes the compiler
environment stack's target-only role concrete: the recursive Result proves
both operands are in `Z`; the active binder frame selects their exact `ℤ`
representatives, computes `%` there, and casts the result back to the Litex
complex observation. Popping the forall body removes those representatives.

`18_RationalNaturalClosures.lit` traces rational `+`, `-`, `*`, `/`, integer
power closure and natural `+`, `*` closure. Ordinary binary rules consume their
ordered recursive children. Integer power consumes `base ∈ Q` and
`exponent ∈ Z`, selects the exact `ℚ`/`ℤ` representatives in the active forall
compiler frame, and casts the native rational power back to the Litex complex
observation. Those representatives disappear when the frame is popped.

`19_NativeConstants.lit` traces native `i`, `e`, and `pi` terms together with
their base numeric memberships. Generated equality uses `Complex.I`,
`Real.exp 1`, and `Real.pi`; `e` and `pi` reach `C` by citing their exact `R`
facts and the existing hierarchy projection. Verified `e $in R+` is the
handoff implemented by Example 21's exact positive-real carrier.

`20_PositiveNaturalCarrier.lit` traces the first exact refined numeric set.
`N+` lowers to the subtype `{n : ℕ // 0 < n}`; a checked positive numeral
constructs that carrier, and `N+ → N` projects its retained native-natural
witness. Verified `1 $in Q+` remains the paired negative boundary because no
positive-rational carrier is introduced by analogy.

`21_PositiveRealCarrier.lit` traces the archived positive-real elimination on
the native-carrier ABI. `R+` is `{r : ℝ // 0 < r}`; closed `1`, `e`, and `pi`
construct it, projection reaches `R` and `C`, and the verifier-inferred
positivity FactId becomes a local proved `have`. The reverse generic constructor
from separate `R` membership and heterogeneous positivity remains fail-closed
without representative coherence.

`22_NonzeroNumericCarriers.lit` traces exact `Z*`, `Q*`, `R*`, and `C*`
carriers on the native ABI. Each carrier is a certified complex-source subtype
that retains base membership and semantic nonzero evidence. Generated proofs
cover all four constructors, base/supercarrier projections, adjacent
`Z* → Q* → R* → C*` widening, and verifier-inferred membership-to-`!= 0`
elimination without a coherence premise. Verified closed reflection
`1 $in Z*` is the paired negative boundary because its closed non-equality
child has no reviewed standalone Lean proof rendering route.

`23_MultilayerApplication.lit` traces exact unary source-layer chains and one
same-layer dependent telescope.
`g(a)(b)` follows the verifier's `FunctionPrefix` WD node: the first call
binds one exact returned function carrier, and the second call separately
consumes `b $in T` plus `In.own` for that carrier. A focused three-layer Rust
regression prevents a two-layer special case. Quantified and named `f(a, b)`
use `FnTelescope.parameter`; ordered domain clauses use a `requirement` node,
and the result has the exact `done` carrier. Generated named values retain
`@f` as a whole telescope value so Lean cannot insert an implicit carrier and
partially apply it. The paired boundary is `f(a)(b)`, which remains a different
and invalid source application shape.

`24_DependentAnonymousFunction.lit` extends that telescope to carriers which
actually mention earlier parameters. Both dependent parameter sets and
argument-indexed return sets lower to `FnTelescope`, so every dependency is
fed by the exact source argument plus its checked membership proof. Compound
anonymous `R -> R` values replay their verifier-owned binder scope and the
retained body-membership closure; direct application additionally checks the
exact `FunctionHead` WD child. The paired boundary is `fn(x R) N {x}`: without
verified body membership in `N`, compilation remains fail-closed.

`25_ExplicitSourceAxioms.lit` is the intentional trust boundary. One
`abstract_prop` declaration emits one visible, source-scoped semantic
predicate specification: its `holds` field is polymorphic and its
`respectsSame` field makes representation invariance explicit. The source
declaration assumes one value of that specification. One explicit `trust`
proposition emits the other visible axiom under its exact source FactId. The
following ordinary fact is a theorem citing that FactId, so the generated file
contains exactly two `axiom` declarations.
An untrusted application of an abstract predicate remains unprovable. Litex
`-strict` deliberately rejects this unsafe source tracer; its release gate is
the ordinary runner plus the compiler's exact axiom-count audit and real Lean.

`29_IndexedTupleCompilerEnvironment.lit` traces a statement whose verifier
owns a genuinely local object check. The returned tuple Result contains the
coordinate value's recursive WD Result plus two dimension-check statement
Results. `StmtResultToLeanCompiler` binds the index in a child compiler
environment, renders the coordinate body there, pops that environment, and
only then publishes the tuple-shape, dimension, and coordinate FactIds.

`30_IndexedSequenceCompilerEnvironment.lit` traces the corresponding local
function-verification layer. The sequence Result retains three named WD
children, the local positive-natural index Store/FactId, and the recursive
return check. `StmtResultToLeanCompiler` consumes them inside one inherited
compiler environment, pops it, and publishes only the sequence membership,
its exact `N+ -> R` function membership, and its defining equality. The next
application proves that Runtime's selected surface-membership FactId remains
the callable contract after that local scope is gone.

`31_FiniteSequenceCompilerEnvironment.lit` adds a domain-premise layer to that
same recursive flow. Two bound-check Results remain outside the function
binder; the parameter membership, `index <= 3` premise, and return check live
inside one inherited compiler environment. The emitted Lean value is the exact
`FnTelescope` described by `finiteSequenceSet`, and the following application
must supply the verifier-owned membership and domain proofs before `.down`
exposes its real result.

`33_NonemptySetWitnessCompilerEnvironment.lit` traces a missing statement and
builtin family together. `WitnessNonemptySet` pushes one inherited compiler
environment, consumes its ordered local proof-step Results, and then compiles
the retained membership check. `ListSetMembership` uses the verifier-owned
selected index and its exact equality child to construct the nested coproduct
witness. Popping the child layer discards every local name; only the outer
`$is_nonempty_set({1, 2})` FactId is published. Function-set witnesses retain a
different return-set check and remain the paired fail-closed boundary.

`34_PredicateBackedWitnessResultComposition.lit` traces the concrete
`witness $P(args)` shorthand that the previous compiler never implemented.
The statement reuses its nested ordinary existential verification, combines
the predicate argument-membership proofs with that existential proof, folds
the result through the compiled predicate definition, and publishes the
primary predicate, parameter membership, and instantiated existential under
the three exact FactIds retained by execution. Multiple-witness and `exist!`
definitions remain separate fail-closed Result families.

`35_SourceAxiomResultBoundary.lit` traces an explicit Litex source axiom. The
compiler validates its recursive forall WD and exact stored FactId, preserves
the declared name as a Lean axiom, and lets the next statement cite that
FactId. Unsupported Results never acquire compiler-invented axioms.

`36_KnownForallResultComposition.lit` traces direct recursive compilation of a
known-forall application. The source axiom publishes one exact forall FactId;
the final fact Result owns one argument and its recursive `2 $in R` parameter
requirement. The compiler checks both, substitutes the retained argument into
the single conclusion, and applies the source Lean theorem without constructing
a mirrored proof IR or searching the execution Runtime.

`43_StrategyDefinitionCompilerEnvironment.lit` makes the compiler-stack rule
explicit for a verified user strategy. `SuccessVerifyStrategyDefinitionResult`
owns the forall WD Result, the parameter-assumption store with its exact local
`FactId`, two ordered proof-step Results, and the final conclusion check. The
compiler pushes one inherited environment for that Result-owned forall body,
compiles `x = x` and `by def $reflexive(x)` there, pops the local identities,
then publishes only the stored outer forall theorem. Ordinary matching can
cite that theorem directly; there is no activation command Result or compiler
pass-through layer.

`44_SettingElaborationResult.lit` records the complementary pass-through case.
A `setting` is consumed by Litex elaboration, so later statement Results already
contain its fresh binders and premise facts. The compiler validates that the
setting Result published no mathematical effects, emits nothing for it, and
compiles the following expanded forall without storing a duplicate setting in
the compiler environment stack.

`45_OrderReflexivityAndNumericComparisonResults.lit` separates two verifier
routes that were previously collapsed into one label-only “number comparison”.
The symbolic theorem owns `OrderReflexivityBuiltinRuleEvidence`, so its forall
Result pushes the binder compiler environment and emits `Litex.Le.refl x`.
The closed comparison owns two recursive `SuccessEvaluateObjResult` children,
including the exact `2 + 3 -> 5` tree. Neither route is selected from a label
or by rerunning verification in the compiler.

`46_RegisteredPredicateCompilerEnvironment.lit` exercises four compiler-only
property bindings whose lifetimes follow successful Results. Each registration
owns its complete recursive `forall_check`, local parameter/domain stores,
proof steps, and checked conclusion. The compiler pushes one inherited
environment, represents `$is_set(x)` as `True.intro` because `x : Litex.Set`
already carries sethood in Lean, and installs domain facts such as
`same_set x y` only in that frame. Definition-projected equalities keep their
exact inferred FactIds. After emitting the reflexive, symmetric, transitive,
or antisymmetric theorem, the compiler pops every binder-local SymbolId and
FactId and publishes only the registered theorem binding in the surrounding
compiler environment.

`47_DefinedPredicateInferenceCompilerEnvironment.lit` makes ordinary
predicate inference recursive and environment-sensitive. Each trusted
`same_set` fact owns typed parameter-requirement and definition-clause
projection Results with exact premise/conclusion FactIds. Top-level projections
become persistent Lean theorems. The same projections inside the registered
transitivity forall are bound to local proof expressions and disappear when
the compiler pops that inherited environment. The source chain then publishes
its exact adjacent-edge projections, folds the visible transitivity theorem,
and lets the final statement cite the inferred conclusion by FactId.

`48_NumericEvalResultComposition.lit` turns a common `eval` command into a
real compositional compiler input. `SuccessEvalStmtResult` owns the exact
source object, evaluated object, and recursive numeric evaluation tree. Its
store effect publishes the final attached equality FactId into the compiler
environment; the following fact cites that ID. JSON v2 projects its reported
store from the canonical common store result, so it no longer prints the stale
pre-attachment `None` FactId formerly held by a duplicated snapshot. Runtime
algorithm evaluations without a recursive computation Result remain the
paired fail-closed boundary.

`49_RegisteredSubtractionAndOrderResultComposition.lit` covers three common
typed arithmetic/order procedures that consume their recursive Result
certificates directly. The compiler validates the Rust rule variant, the exact
ordered comparison child, the subtraction operand reversal, and strictness
before selecting the Lean adapter for `v <= u -> 0 <= u - v`,
`v < u -> 0 < u - v`, or the strict-to-weak `a > b -> a >= b` conversion.
Reordering semantic children fails closed.

`50_SetExtensionResultComposition.lit` compiles the two directional children
of `by extension` in one inherited compiler environment and closes the exact
set equality with `Litex.Same.setExt`.

`51_FiniteEnumerationResultComposition.lit` retains every finite assignment,
its local equality FactId, and its conclusion Result. Each branch is compiled
in its own inherited environment.

`52_IntegerRangeIterationResultComposition.lit` adds recursive endpoint
evaluation and ordered range assignments to the same branch-owned model.

`53_RuntimeResolvedComparisonFromDefinitionResults.lit` checks that prior
definition Results publish the exact object bindings needed to validate and
compile a later runtime-resolved comparison and its typed inference child.

`54_ComplexAlgebraicCalculation.lit` replays exact complex normalization,
ordered nonzero children, and division/power side conditions without asking
Lean to rediscover the source proof.

`55_TemplateSequenceInstantiationResult.lit` compiles one reviewed template
family, one created instance, and one reused instance directly from their
successful Results.

`56_StructuredIntegerInductionResult.lit` pairs closed numeric membership with
a structured induction Result whose base, step, local assumptions, conclusion
checks, and outer store remain explicitly nested.

`57_KnownForallFactIdProvenance.lit` proves two grouped conclusions from one
stored universal. Each indexed conclusion retains the complete source forall,
its exact FactId, and a structural conclusion location. The second application
also reuses a parameter-membership FactId recursively produced while compiling
the first conclusion; corrupting either the source FactId or location fails
closed.

`66_LocalTypedSetDefinition.lit` lowers a local
`have E power_set(R) = {x R: ...}` inside a named theorem. The definition
publishes its exact type, equality, subset, and elementwise facts; the
set-builder/power-set proof consumes a typed child for the parameter subset.

`67_LocalRealCompleteness.lit` uses the general real least-upper-bound builtin
inside a named theorem. Its local proof step validates the builtin theorem ID,
the explicit `S subset R` and nonempty premises, the nested pointwise
upper-bound premise, and the conclusion FactId before calling the proved Lean
adapter. The paired negative test keeps greatest-lower-bound support explicit
as an uninstalled adapter rather than inventing a proof.

`68_LocalTransparentSetMembership.lit` defines a local set builder and then
proves `0 $in E`. The verifier records the existing generic one-pass
transparent-definition transformation with the exact defining equality
FactId; the compiler validates that record, unfolds only `E`, and recursively
replays ordinary literal set-builder membership. There is no theorem-name or
set-name specialization.

`69_RealCauchyFromCompleteness.lit` is the broad real-analysis regression. It
derives convergence of every real Cauchy sequence from the general
least-upper-bound interface, using the Archimedean interface to select named
positive-natural common tail indices. The generated proof exercises exact
function carriers, concrete predicates, nested forall/existential transport,
local typed set builders, transparent membership, LUB observers, algebraic
equality rewrites, and typed order transitivity. It introduces no
sequence-specific builtin or project axiom.

Generated `.lean` files are review artifacts, not editing surfaces. A new
compiler feature must add the next numbered same-name pair. Unsupported
statements, objects, facts, or proof routes fail closed.
