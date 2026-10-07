# Litex compilation to Lean design

This proposal preserves Litex's pure-set mathematics while making ordinary numeric, set and function results usable in Lean and Mathlib. The recommended architecture keeps native Lean representations and proves their correspondence with a concrete set-theoretic model. The architecture and numeric encoding policy remain open user decisions. No compiler or semantic change is implemented by this document.

## A representative source and its intended export

The current source in [b03.lit](../examples/test_function_sets/basic/b03.lit) is:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

The installed release binary accepted this exact file with exit 0 and Normal run JSON `success: true`:

```sh
target/release/litex -strict -f examples/test_function_sets/basic/b03.lit
```

The existing [negative source](../examples/test_statements/negative/have_fn_equal_stmt/ill-defined-function-body.lit) is:

<!-- litex:skip-test -->

```litex
have fn f(x R) R = 1 / x
```

It returned exit 1 and `success: false`; function-body WD could not prove `x != 0`. Lean's totalized division must not make this invalid Litex definition exportable.

The intended native consumer below is an acceptance shape, not generated or verified code:

```lean
-- Proposed native interface.
def reciprocal (x : ℝ) (hx : x ≠ 0) : ℝ := 1 / x
-- Generated proof plus a proved adapter must supply the corresponding
-- native equality for reciprocal 2, without proving the goal again.
```

The compiler must replay the function definition, its checked return membership, the application WD, the nonzero proof and the defining equality. A native consumer may use a subtype domain instead of a proof argument; the bridge between them must be proved. This example exercises external WD and useful Mathlib output. Set foundations and graph identity additionally need the empty-function control below.

## Current semantics and implementation boundaries

[Obj](../src/ast/obj.rs) explicitly describes a pure-set model. The [IsSet builtin](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof_by_builtin_rules/is_set.rs) returns:

```rust
Ok(Some(IsSetFactSearchProofByBuiltinRule::AlwaysTrue(
    IsSetAlwaysTrueBuiltinRuleProof {},
)))
```

This occurs after enclosing WD checks. A numeral, a function, a tuple and a numeric domain are all sets. Membership and equality relate ordinary objects; there is no separate runtime collection sort. The meta-level object carrier is not an internal universal set, and comprehension is bounded.

The [parameter types](../src/ast/param.rs) distinguish `A set` from `x A`: the first quantifies an object with sethood; the second introduces membership. Function parameter and return sets are fixed relative to the entire function signature. Guards and bodies may depend on its arguments; ordinary quantifier binders remain sequential. The current [binder WD](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/binder.rs) rejects own-parameter references in return sets, despite an older contrary comment in `obj.rs`.

Numeric membership is knowledge about the same value. Arithmetic has its own semantics: field operations use complex arithmetic, with nonzero requirements for division. Therefore these proposed arithmetic controls must retain their usual meanings:

<!-- litex:skip-test -->

```litex
# Illustrative acceptance cases; not executed in this planning task.
1 - 2 = -1
1 / 2 $in Q
```

A binder in `N` does not authorize lowering subtraction to truncated `Nat.sub` or division to `Nat.div`. Host representation must follow the resolved operation and proved bridges, rather than the narrowest membership fact available later. Powers, logarithms, roots and remainder each need their own precise branch contract.

Functions have exact complete input domains, including guards. Their declared return sets are upper bounds and must not determine graph identity. Tuples are finite functions with one-based coordinates. The actual [empty-function source](../examples/proof_nodes/equal/by_builtin_rule/empty_function_graph_identity.lit) contains:

```litex
()={}
have fn empty_fn(k {}) R=0
empty_fn={}
```

A representation that keeps function values permanently disjoint from sets cannot preserve these equalities. Native `Prod`, records and function types remain useful representations only with the corresponding graph proofs.

The current Rust crate exposes no Lean compiler module or compiler binary. The retained `lean/stmt_result_to_lean_compiler.sh` invokes an absent binary. The historical `lean/` examples and coverage reports do not establish compiler support for the current `src/` tree. `litex_semantics_in_lean/Core.lean` is a separate, unintegrated proposal. Neither retained Core should be accepted as a foundation without new kernel checks and semantic correspondence proofs.

Current CLI uses `-strict -f` and emits Normal JSON with top-level `success`. Old skill commands containing `-compact -runner` were rejected with exit 2 in this task. The successful reciprocal JSON also renders its definition without the return annotation in `statement`, although its stored function membership retains `R`; display text is therefore unsuitable as compiler input.

## Why a common mathematical denotation is necessary

The old representation `Set { Carrier : Type }` and heterogeneous equality carry useful ideas, but they do not by themselves model all objects as sets. The current [set WD](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs) checks only child WD for operations such as `power_set`. Thus an expression such as `power_set(1)` needs a mathematical interpretation under the existing contract, even though it is not a common numeric use case.

Giving each numeric value an empty membership extension would make all numbers equal by global extensionality. Adding an unconstrained bridge relation would instead make equality transport unsafe. The retained Core also distinguishes object equality from a separate `SetEquivalent`; the new model must establish both argument positions of membership congruence.

The recommended mathematical contract is the following schema. These are proposed interfaces, not complete Lean declarations:

```lean
Representation α: a fixed map denoteα : α → ZFSet.{u}
Same x y := denoteα x = denoteβ y
In x A := denoteα x ∈ denoteβ A
```

Representation is selected explicitly by a declaration or construction. A later membership fact must not silently replace it. There is no blanket default instance asserting that every Lean type has a valid Litex interpretation. Different native views of an object share proved equal denotations.

This definition gives one semantic equality and proves symmetry, transitivity, membership transport on either side and extensionality from the underlying set model. Numeric observation laws become consequences of correspondence proofs. They do not define a second observer-indexed equality. Recover native `x = y` only when the specific representation is proved injective.

`ZFSet` is Mathlib's existing mathematical model, constructed as an extensional quotient of pre-sets. It supplies definitions and proved interfaces for powersets, images, well-founded membership and function graphs. It is a candidate semantic foundation, not an invented `axiom LitexObject : Type`. See the [Mathlib ZFC documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/ZFC/Basic.html). Its presence does not automatically prove the numeric and function correspondence needed here.

For unrestricted source `forall A set`, the model-backed translation quantifies `A : ZFSet.{u}`. It must not narrow the quantifier to a package of native element types. Sethood may reduce to a trivial proposition in a pure-set model, but only because every denoted value is actually a set; its source FactId remains bound to the corresponding proof. This is different from erasing sethood while leaving numeric and function objects uninterpreted as sets.

## Native presentations and universe constraints

An exact native presentation of a source set `S` needs more than an element type:

```lean
-- Mathematical schema.
Carrier : Type v
encode : Carrier → ZFSet.{u}
injective : Function.Injective encode
membership : ∀ z, z ∈ S ↔ ∃ a : Carrier, encode a = z
```

Injectivity prevents distinct representatives of the same semantic member from being counted twice. Exact coverage prevents missing source members. For a generic model set, its member type has a proved smallness property; Mathlib's smallness/shrinking interfaces can provide an appropriately small carrier. Native presentations, general model objects and their Lean universe levels must be checked separately.

Use one sufficiently large model universe for a compiled unit and coherent lifts at module boundaries. This is not a source-level set containing every model object. Set builders and function spaces still range over actual bounded sets. Constructing a set from a family requires the appropriate small index carrier; never form `range` over all of `ZFSet` to manufacture a universal set.

Ordinary numerical subsets can use native predicates and subtypes. Mixed sets may use a certified common presentation or the model's member presentation. A raw sum of element carriers is not yet an exact presentation: `union({1}, {1})` must have one semantic element, not two tagged copies. Any quotient or deduplication must use equality of denotations and come with the injectivity and coverage proofs.

## Numeric hierarchy and operator contracts

Choose and prove one injective complex encoding `encodeC : ℂ → ZFSet`. Define the other number representations through the native embeddings:

```lean
-- Proposed mathematical definitions.
encodeN n := encodeC (n : ℂ)
encodeZ z := encodeC (z : ℂ)
encodeQ q := encodeC (q : ℂ)
encodeR r := encodeC (r : ℂ)
N := ZFSet.range encodeN
Z := ZFSet.range encodeZ
Q := ZFSet.range encodeQ
R := ZFSet.range encodeR
C := ZFSet.range encodeC
```

The same natural value is consequently the same set object in every numeric domain. Prove cast compatibility, hierarchy inclusion, exact membership characterization and native injectivity. `N+`, `R+` and nonzero variants add their actual properties; they are not aliases of their bases.

Each operator contract names its source WD branches, native operation, result membership, denotation law and equality/order elimination. For division, retain the source nonzero proof even though Lean defines division at zero. An `R` representative permits native real order; membership in `C` alone must not permit real comparisons. A new narrower membership can expose another native view through a proved adapter without changing the original object's denotation.

An encoding of complex numbers into well-founded sets is a substantive Lean construction obligation. The first foundation slice must demonstrate an actual injection and useful native elimination. A structure field assuming injectivity, or a theorem taking the needed coherence as an unproved argument, does not complete this obligation.

## Functions and other object families

For one source layer, combine its fixed domains into an input product and apply the guard as a predicate on that product. A native presentation has the shape:

```lean
-- Proposed unary guarded presentation.
{x : DomainCarrier // Guard x} → ReturnCarrier
```

Its denotation is the exact graph over encoded admitted inputs. Prove uniqueness, graph membership, applicability, result membership and agreement with native application. The graph does not include a codomain label, so two return upper bounds for the same graph do not change the source function object. Semantic application must respect equal input denotations and be independent of the membership/guard proof selected by the verifier.

An empty input domain has an empty graph. Current [function signature parsing](../src/parse/object/primary.rs) rejects a zero-argument function with `fn expects at least one parameter`; the empty tuple `()` is an existing object, not authorization for `fn()`. Internally, an empty parameter vector has one input assignment, as recorded by the `internal_zero_parameter_signature_has_one_input_assignment` kernel test; preserve both this internal invariant and the source rejection. The graph-key interpretation of unary tuple input `f((x,y))` versus one two-argument layer `g(x,y)` needs a source-derived contract before implementing n-ary functions. Existing WD and domain comparison count argument positions per layer; binder grouping and return upper bounds do not determine graph identity. The arity rejection alone does not prove differently parameterized functions unequal.

The application result consumes the exact function membership, argument membership and ordered domain-clause proofs from WD. A proof argument is an implementation of Litex's external evidence, not a new mathematical input to the function. Native proof irrelevance and graph uniqueness justify this distinction.

Preserve `f(a,b)` as one source layer and `f(a)(b)` as two layers. Lean currying must not repair wrong source arity. `have fn ... by exist!` retains its existence and uniqueness evidence before selecting a value. The current source does not support own-parameter-dependent function domains or return sets; Lean's dependent types must not silently enlarge that source language.

The important object mapping families are:

| Source family | Native view and required set meaning |
| --- | --- |
| Literals and standard numeric sets | Native numbers and exact encoded ranges |
| Arithmetic, integer, transcendental and complex operations | Operator-specific native operations with source WD and denotation laws |
| Finite literals, set builders and intervals | Exact native finite/predicate presentations; bounded set construction |
| Union, intersection, difference, family operators and powerset | Actual model set operations and certified native presentations |
| Functions, function spaces and ranges | Exact-domain graph coding, graph sets and image theorems |
| Cartesian objects and tuples | Native products or finite functions, encoded as the source's one-based function graphs |
| Sums, products, reduce and finite statistics | Native finite iteration on exact member presentations; preserve inclusive/half-open bounds and source side conditions |
| Structs and field applications | Native records as presentations of the source finite-function view; retain field order, laws and graph identity |
| Templates | Scoped declaration families preserving source parameter identity and instantiated definition facts |

An object is not semantically supported merely because a target wrapper can store its syntax and prove reflexivity. Every supported family needs actual construction, elimination, congruence and a downstream use.

## Foundations and source assumptions

Separate named fixed foundations from user assumptions. The current regularity branch checks nonemptiness and stores:

<!-- litex:skip-test -->

```litex
# Shape produced by release regularity_axiom(A).
exist x A st {intersect(x, A) = {}}
```

The target adapter must prove that exact conclusion from the model's regularity theorem. Choice uses proved nonemptiness of each factor. Replacement uses a checked functional relation on a bounded source; the current interface permits a partial relation and must not be strengthened to totality. Zorn requires its actual order and chain-upper-bound premises. Each named release needs an explicit correspondence theorem, rather than an emitter-generated axiom.

Concrete `prop` definitions become predicates on denotations with checked admissibility clauses. An `abstract_prop` is an arbitrary predicate interface and can be represented as a predicate parameter on model objects; it does not itself prove applications. Equality substitution then follows from native equality of those objects.

User `axiom`, `trust` and trusted object introductions remain exact assumptions. A proposed conditional export is:

```lean
-- Proposed export policy; no source fact is made true by the compiler.
theorem result (source_assumption : P) : Q := ...
```

A proof-only export should reject unresolved source trust. Conditional export may retain explicit hypotheses and witness parameters with their required laws. No unsupported builtin or missing WD edge may create a new assumption. `-strict` rejects user trust and axiom statements but allows fixed foundation releases; it is not a substitute for Lean dependency auditing.

Lean can report transitive axiom dependencies with `#print axioms`. The intended safe boundary permits the usual Lean/Mathlib foundational dependencies and excludes newly introduced project assumptions or proof holes. See the [Lean axiom reference](https://lean-lang.org/doc/reference/latest/Axioms/). Checking one compiled theorem verifies that proof under its stated interpretation and assumptions; it does not by itself prove global Litex soundness or compiler semantic preservation.

## Result contracts and exact proof replay

Keep the current Exec, Verify and Infer decomposition. An actual fact execution result already preserves:

```rust
pub struct ExecFactStmtSuccessResult {
    pub verify_result: VerifyFactResult,
    pub store_and_infer_result: StoreFactAndInferResult,
}
```

Known-forall application retains a source FactId, conclusion location, substitutions, argument matching proofs and instantiation requirements. Function WD retains its selected function-set source, child WD proofs and requirement proofs. Scoped proof results retain local environments for resolving citations. These are appropriate compiler inputs; JSON descriptions and failed search candidates are not.

Four concrete missing return contracts need attention before general replay:

1. **Theorem binders and assumptions.** The [named theorem helper](../src/execute/execute_def_thm_stmt/exec_def_thm_stmt.rs) discards parameter-introduction evidence and uses `let _ = runtime.store_fact_and_infer(dom, ...)`. Retain these stages using the already established `introduced_params` and `assumed_dom_facts` pattern in [VerifyForallFactSuccess](../src/execute/execute_fact_stmt/verify_forall_fact/result.rs).
2. **Definition inference.** `StoreHaveObjAndInferResult { stored_fact_ids: Vec<FactId> }` and the named-function store compress existing infer results into IDs. Retain the real `StoreFactAndInferResult` outputs so later cited consequences have derivations.
3. **WD registration.** `ByKnown { obj, wd_id }` cites a cached certificate, but [storage](../src/store_fact_and_infer/store_fact_and_infer.rs) allocates that ID without returning its link to the earlier checked WD occurrence. Return the registration with an exact proof owner; keep the current tree and sharing before considering a new flattened graph.
4. **Registered law identity.** Some reflexivity, symmetry and transitivity uses cite only a predicate name. Link them to the actual proved registration in its owning scope. Current closed Rust enums already identify builtin routes; a serialized fingerprint format is a later compatibility decision, not an existing implementation fact.

Illustrative result additions must follow the existing pipeline, for example:

```rust
// Proposed retained stages; precise ownership to be settled before editing.
introduced_params: IntroduceTypedParametersResult,
assumed_dom_facts: Vec<AssumeDomFactResult>,
parameter_stores: Vec<StoreFactAndInferResult>,
```

There is also a required capture boundary before compilation. Current [RunLitexCodeResult](../src/run/run_command_outcome.rs) keeps `Vec<ExecStmtResult>` beside rendered `Vec<String>`; [parse_and_exec_token_block](../src/run/run_litex_code.rs) returns `(String, ExecStmtResult)` and discards the original parsed statement. The named theorem success does not retain its declaration name. Current file/repository results also do not own the global module table after Runtime is dropped. Results alone are therefore not yet a standalone compilation package.

The smallest proposed statement capture is:

```rust
// Proposal, not an existing type.
pub struct CheckedStatement {
    pub statement: Stmt,
    pub result: ExecStmtResult,
}
```

Together with ordered file/module/export identities and an immutable closure of exact citation payloads, this retains declaration semantics without duplicating the proof log. Existing knowledge-base import hits restore environments and skip source execution evidence; the first compiler path should use the current cold strict-import route. Later cache support must persist and verify replay certificates, rather than treating a cached environment as a proof.

Collect this package while Runtime is alive. Local environment tables resolve entities; they must not be scanned to discover an unrecorded proof. The source name, binder identity, statement order, module owner and persistent/local distinction must all survive. No AST field or Env/Runtime state-management change is authorized by this plan.

The compiler then matches supported success variants exhaustively. Known facts become exact named terms, forall applications become the recorded instantiation, constructors consume their ordered child proofs, and builtin variants call reviewed Lean lemmas. Fixed arithmetic adapters may use a checked reflective proof or bounded tactic implementation of that selected route; they must not search for an unrelated proof of the final goal.

Facts introduced inside a theorem, case, witness or transactional `try` remain there. Failed statements do not publish declarations. A later proof cannot cite a dead FactId or use a WD proof whose binders have escaped. Unsupported cases produce structured diagnostics and preserve existing output; they never produce `sorry` or a partial usable theorem.

## Responsibility and dependency order

| Owner | Contract |
| --- | --- |
| Lean semantic Core | Concrete model, fixed representation maps, injectivity, exact set presentations, graph semantics and native elimination |
| Lean rule adapters | Proved meaning of each supported verifier rule and named foundation |
| Kernel results | What succeeded, premises consumed, effects stored and scopes owning citations |
| Compiler | Native representation selection, source declarations, exact certificate replay and diagnostics |
| Adapter | Useful ordinary Lean interfaces obtained through proved representation bridges |
| Native consumer | A theorem statement containing only ordinary Lean/Mathlib concepts |

The dependencies run from source semantics to model definitions and representation laws; from those laws and verifier evidence to rule adapters; from execution results and adapters to generated proofs; and from proved elimination to native consumers. Object, statement and proof syntax stay in Rust. The target Core does not need to copy all AST enums.

## Implementation phases and acceptance

1. **Fix the foundation decisions.** Choose model-backed native generation versus all-model generation, choose numeric encoding visibility, and settle source operations with incomplete meanings. Record actual CLI and existing-result boundaries. The current source and old generated examples are separate baselines.
2. **Build a small complete Core.** Demonstrate an actual complex encoding, the shared numeric hierarchy, a finite/predicate set presentation, equality/membership transport and faithful native equality elimination. Include one extensionality example and the empty graph identity. No project axioms or proof holes.
3. **Complete one evidence path.** Preserve source declarations, theorem binders, exact assumptions, definition infer results and WD registration for the reciprocal path. Reuse current source-semantic result types. Test both valid and missing-guard paths and scope rollback.
4. **Compile the reciprocal source.** Generate declarations from successful execution results and verify them with the pinned Lean/Mathlib toolchain. Add a same-name source/generated pair only after both stages are genuinely supported. A handwritten adapter supplies a native consumer without a second proof of the mathematical goal.
5. **Add logical and mathematical families.** First exact citations, definitions, quantifiers, conjunction/disjunction, existential witnesses, cases, contradiction and induction. Then function equality, sets, images, replacement, choice, regularity and Zorn. Expand arithmetic and aggregate rules by reviewed evidence families, not by raw object-count coverage.
6. **Stabilize export and maintenance.** Specify versioned representation/rule contracts, generated drift checks, exact declaration preservation, unsupported diagnostics and native-consumer gates. Add full serialization only when an external certificate consumer requires it.

The first end-to-end acceptance has four independent obligations: the exact Litex source verifies; the compiler consumes its actual successful route; Lean checks the generated proof without extra project assumptions; and a native theorem uses the proved adapter while keeping the intended statement and hypotheses. A generated proof of a weakened or differently quantified statement does not pass.

Negative controls include the unguarded reciprocal, a zero call, wrong arity/layer, zero-argument function syntax, wrong return membership, altered certificate target, missing child proof, dead local citation, and unresolved source trust in a proof-only export. Preserve the source arithmetic meaning and empty graph identity. Also test conditional trust inside its original binder scope: a trusted witness in arbitrary `A` cannot produce an unconditional inhabitance theorem. Count support by these semantic contracts and real native uses, rather than accepting wrappers that only prove object reflexivity.

Before each implementation batch, classify its actual semantic fan-out. Result additions require producer/consumer contract checks; model or public representation changes require focused real Lean checks plus relevant kernel gates. The installed-binary reciprocal positive and negative baselines establish current source behavior. The independent foundation probe below establishes mathematical feasibility for a candidate; production Core interfaces and compiler stages remain unimplemented.

## Foundation feasibility evidence

An independent draft [ModelFeasibility.lean](../tmp/2026-10-07/litex-to-lean-foundation-plan/ModelFeasibility.lean) passed the real Lean 4.31.0 kernel with exit 0:

```sh
# Working directory: lean
lake env lean ../tmp/2026-10-07/litex-to-lean-foundation-plan/ModelFeasibility.lean
```

It proves ten declarations: a candidate complex encoding's injectivity and equality elimination; its exact internal membership characterization; the encoded natural range's inclusion in the complex range; reconstruction of a model set from its members; graph application/uniqueness; graph membership in a function space; empty-domain graph identity; the source-shaped regularity conclusion; and existence of a selecting function graph with codomain the union of the family. All ten `#print axioms` checks report only `propext`, `Classical.choice` and `Quot.sound`. The [kernel evidence](../tmp/2026-10-07/litex-to-lean-foundation-plan/kernel-evidence.json) records the exact command and declaration outputs.

The checked candidate is:

```lean
noncomputable def codeComplex (z : ℂ) : ZFSet.{0} :=
  Ordinal.toZFSet (Ordinal.typein (@WellOrderingRel ℂ) z)
```

This removes the existence/universe uncertainty for an injective `ℂ → ZFSet.{0}` map. It is not selected as the production encoding. Its checked membership law is:

```lean
codeComplex x ∈ codeComplex y ↔ (@WellOrderingRel ℂ) x y
```

Thus numeric interiors become a choice-selected well order, rather than conventional number constructions. Injectivity alone does not establish a model of every Litex builtin, all structural/numeric equalities or the published von Neumann convention. The choice graph theorem supplies graph uniqueness and element selection; connecting it to Litex's exact `IsChoiceFunctionFor` predicate, application WD and stored source FactIds remains compiler/Core work.

## Decisions still open

**Generation architecture.** Native values with proved set denotations preserve useful Lean interfaces but front-load correspondence proofs. Generating only `ZFSet` terms gives direct set-theoretic reasoning but needs more adapter work for every native consumer. Both preserve the source pure-set model. Changing later will affect public generated interfaces and proof adapters; choose before building the first Core.

**Numeric interiors.** An implementation-fixed complex set encoding can remain outside the public source rules while supporting native arithmetic. Alternatively, publish the von Neumann natural-number convention, including `0 = {}` and `0 $in 1`, and require every larger numeric domain to reuse those same objects. Neither convention follows merely from the current `AlwaysTrue` sethood rule. Publishing a convention increases future compatibility obligations.

**Empty absolute family intersection.** Current WD accepts the child-only form:

<!-- litex:skip-test -->

```litex
# Illustrative boundary; not run here.
family_intersect({})
```

However, current intersection membership rules require nonempty families, and one equality-rule comment describes empty absolute intersection as a universe class. A universal class cannot be an internal set in this model. Choose either a nonempty-family WD requirement or an explicit totalized set value, such as the empty set with suitably restricted laws. This is an unsettled denotation contract, not a demonstrated soundness failure. Keep it unsupported in the compiler until the source decision is fixed. Existing `index_intersect(I, X, A)` has an explicit ambient set and separate obligations; it does not silently settle this absolute operator's meaning.

The immediate next implementation slice should begin only after the architecture and numeric policy are chosen. It should prove the foundational correspondence and make the reciprocal source genuinely exportable; broader object and rule coverage follows those contracts.
