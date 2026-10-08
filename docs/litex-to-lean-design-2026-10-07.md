# Litex compilation to Lean design

This proposal preserves Litex's pure-set mathematics while making its results usable in Lean and Mathlib. The user's latest October 8 direction preserves native numeric values and selects Litex-owned representations, constructors and operations for everything else. Native sets, arrows, products and raw arithmetic are external adapter views, not the primary nonnumeric object model. No compiler or semantic change is implemented by this document. Complete mathematical interpretation remains a proof obligation.

The current object-model design is collected in [Litex object model for Lean](litex-lean-minimal-core-design-2026-10-08.md). Specify which objects exist and their basic semantics before execution or proof replay. Keep generic source representatives and ordinary Same/In/IsSet facts. The separate `Litex.Num` proposal is withdrawn. Internal operations stay Litex-owned even when numeric storage or an implementation uses native values. The previously proposed native guarded function arrow is withdrawn as an internal representation; it is only an external adapter view. Earlier alternatives and legacy audits below are historical background.

## Current priority: object contracts before proof replay

Use the retained legacy object-model concepts as a reference and the current source semantics as authority. Current equality classes own equality evidence; how to compile their proof paths is a later design problem. Do not derive the new execution design from retained Core rule registries or historical generated files.

The immediate deliverable is a per-family Litex representation and mathematical contract: construction and admissibility, membership/sethood, equality meaning and external adapters. Function spaces, function values, application expressions and images are distinct Litex-owned objects/interfaces. Internal function construction retains the source signature and body operations; internal application retains each source argument layer. A native map is a secondary adapter view. The current equality-class pipeline later supplies the proofs required by those mathematical contracts.

The source `FnObj` is an application expression, not a function-value declaration. Its target stays behind Litex application operations/objects. `f(a,b)(c)` retains two application layers. A function value has exact-domain graph identity; written return bounds are output constraints, not graph identity labels. The current source fixes parameter domains and return sets relative to their own binders; guards and bodies can depend on those binders. The object card records Litex-owned function interfaces without specifying verifier search or Result emission.

## Retained baseline and historical audit

The retained v2 header already has native N/Z/Q/R/C carriers, generic heterogeneous membership, exact-carrier representative extraction, numeric cast bridges and faithful native equality elimination. A source object may remain `a : α` while `In a R` and `In a C` are facts. These are useful existing contracts, not provisional deficiencies. Preserve them unless a specific source-semantic mismatch requires a change.

The first repair is genuine IsSet evidence and coherent set views. `lean/Litex/Core.lean` currently mentions IsSet without defining it; retained example 1 erases sethood assertions to True. Every supported WD object, including numbers, must obtain sethood with the source's meaning. A separate number wrapper would not solve this obligation.

Two further mathematical gaps need bounded repairs before their affected source rules are supported. First, `In a C` stores a no-observation Same witness, while native equality elimination consumes an observed witness; the current extensible bridge classes do not by themselves prove uniqueness of every numeric member representative. Second, general Same between set objects must preserve their membership extensions; the current header explicitly does not derive SetEquivalent from arbitrary Same. Restricting bridge admission and proving the appropriate coherence laws may change Core internals, but preserves the useful public concepts.

Function support later requires calls to respect Same inputs and exact-carrier calls to agree with ordinary calls. Full pure-set graph identity, foundational releases and general set constructions are a larger, separate mathematical extension. The current object/reflexivity/R-to-C MVP does not justify requiring a complete rewrite before showing a working slice.

The current Rust checkout has no active statement-result Lean compiler module or executable. Restoring the producer against current Result types is real implementation work; it is not evidence that the old representation architecture needs replacement. Retained examples and README coverage are historical assets, not a running compiler gate.

Four handwritten interface checks importing the retained Litex library passed Lean 4.31.0 via stdin: generic reflexivity, generic R-to-C membership, native complex one reflexivity and native complex one membership in R. Each reported only propext, Classical.choice and Quot.sound. This validates those retained library interfaces; it does not validate IsSet, the missing coherence laws or a current compiler.

## Semantic arithmetic API and native adapters

The current recommendation is to give Litex its own semantic operation API and prove native-operation correspondence in Core, while retaining native numeric results. A generator spelling `Litex.add` need not create a new universal object type or a second expression AST. Internally the operation may use Mathlib's native arithmetic once its source admission and interpretation are proved.

There are three materially different alternatives:

| Approach | Meaning and tradeoff |
| --- | --- |
| Emit native operators directly | Concise, but the compiler must choose the correct operand interpretations and source operation branch before each emission |
| Emit Litex semantic operators and use proved native bridges | Recommended: Core owns admission, value meaning and congruence; the compiler replays WD and rule evidence; an adapter exposes native Mathlib operations |
| Introduce uninterpreted operations and algebra axioms | Does not establish that actual Litex operations correspond to the intended mathematics; do not use for proof-only compilation |

The intended mathematical API has this shape; the result carrier is deliberately not selected by this sketch:

```lean
-- Proposed operation and theorem contracts.
Litex.add a b haC hbC
Litex.add_in_C : In (Litex.add a b haC hbC) C

observeC (Litex.add a b haC hbC) Litex.add_in_C =
  observeC a haC + observeC b hbC
```

The inputs may have independent host types `α` and `β`. Their C-memberships are ordinary source facts supplied by the actual WD Result. The mathematical value returned by the operation does not change when the caller uses another proof of those same facts or a Same representative of either input. Prove result membership/sethood, the observation equation, input congruence and proof/view independence before claiming support.

Subtraction, multiplication and division follow the same source-owned contract. Division additionally consumes the verified source condition:

```lean
-- Proposed checked call shape.
Litex.div a b haC hbC (hb0 : ¬ Litex.Same b (Litex.numeral 0))
```

The adapter must convert that exact semantic nonzero evidence to the native denominator condition. A total native division operation does not authorize a source division by zero. Lean proof arguments implement external WD evidence; they do not add mathematical inputs to the source function.

Native bridges must preserve the source operation, not select an arbitrary operator called `+`, `-`, `*` or `/`. Real and complex views can expose their reviewed native operations. A natural-number view does not support unconditional source subtraction or field division: native `Nat.sub` and `Nat.div` would turn the source values `1 - 2` and `1 / 2` into zero. Use proved preservation laws and the exact source domain conditions for every specialization. The [Mathlib homomorphism definition](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Algebra/Ring/Hom/Defs.lean) illustrates the relevant operation-preservation contract; it does not supply Litex's correspondence proof automatically.

Source literals may similarly be exposed through `Litex.numeral`/exact-rational constructor interfaces. For example, `1=1` would ask for `Same (numeral 1) (numeral 1)`, and `$is_set(1)` would ask for `IsSet (numeral 1)`. Their actual result representation may initially use native complex values. Creating a separate number wrapper solely to rename ℂ is unnecessary; choose a separate carrier only when it owns an independently justified invariant or semantic responsibility.

This API does not resolve arbitrary-host interpretation by itself. Operators, literals, membership and equality all still use the one coherent object model. Keeping operands in a payload-only `AddExpr` and proving reflexivity would not establish mathematical addition; an AST representation would also need a proved evaluator and denotation laws. The intended first implementation is semantic functions with proved native bridges, not a duplicate target AST.

## Object meaning and numeric representation

The recommended policy distinguishes the source mathematical object, its Lean representative, and facts about that object. Each Lean term has a fixed host type, while source mathematical classification accumulates through ordinary propositions. `In`, equality and user predicates all belong to this fact layer; membership must not mutate the representative or its host type.

Native numeric representations are now the selected baseline. Preserve the legacy numeral lowering and reviewed native carriers rather than adding a separate `Num` record. The retained generated numeral examples use native `ℂ`; N/Z/Q/R/C expose their existing native carriers. This does not authorize arbitrarily selecting Nat arithmetic for an operation with different source semantics. The recommended public operation API remains Litex-owned, with proved native bridges. The table records native lowering and later interpretation obligations, not a selected production set encoding. Keep the notation distinction: Lean `ℂ` is a type; source `C` is a mathematical set object. Do not put `: Litex.C` on a numeral as though the source set itself were a Lean type.

| Source object | Recommended representative |
| --- | --- |
| Integer literal `1243` | `(1243 : ℂ)` |
| Exact decimal `1.25` | `((5 : ℂ) / 4)` |
| `i`, `e`, `pi` | Canonical complex constants, with their reviewed mathematical meaning |
| A fresh or quantified identifier `a` | `a : α`, with a fixed interpretation and independent source facts |
| `a + b`, scalar division and other intrinsic numeric results | New canonical complex value, after consuming the exact WD evidence and native views |
| Integer operations such as remainder or gcd | Reviewed native integer computation, then canonical embedding into `ℂ` |
| `N`, `Z`, `Q`, `R`, `C` and constructed sets | Litex-owned set objects and membership laws; exact native carriers are adapter views |
| Tuples | Litex-owned one-based finite-function objects, with optional native product adapters |
| Named/anonymous functions and function spaces | Litex-owned construction, signature, application and graph semantics; native callable forms are adapters |
| Structs and templates | Litex definition-owned objects/fields and declaration families; native records are adapters |

The first invariant is coherent meaning: facts and views cannot change the value represented by a term. One possible way to prove the full pure-set obligations is a fixed interpretation into a concrete model. The following is an alternative mathematical schema, not standalone Lean source or a newly selected public ABI:

```lean
meaningα : α → ZFSet
Same a b := meaningα a = meaningβ b
In a A := meaningα a ∈ meaningβ A
IsSet a := ∃ s : ZFSet, meaningα a = s
```

Here interpretations are target compilation data, not source typing or numeric membership assumptions. A bare arbitrary Lean type does not supply a mathematical interpretation by itself; previous generic signatures suppress this metadata. A complete implementation must supply it through a fixed Core interpretation context or a coherent representation interface. It must not choose a new map each time it proves membership. In a shared context, equal values of the same native carrier use the same interpretation. The canonical complex interpretation is always the one fixed injective complex encoding; a generic carrier later instantiated as `ℂ` must remain compatible with it. Conflicting interpretations need distinct certified host representations, never a changed meaning for the same value.

This model makes `In` an ordinary binary proposition, exactly like a concrete predicate on the two interpreted objects. A source predicate may be defined on model values, or provide a proved Same-congruence theorem for its native representation. Predicate implementations cannot distinguish irrelevant host metadata when source equality identifies the represented objects. Equality transport in both membership arguments follows from equality of meanings. Native equality lifts within the fixed interpretation; native equality is recovered from Same only at a proved faithful presentation.

For constants, fix `meaningℂ z := encodeComplex z`. Then the two requested examples have distinct evidence routes:

```lean
-- Intended compiled statements and adapters, not generated output.
-- Source: 1 = 1
Litex.Same (1 : ℂ) (1 : ℂ)
-- Proof adapter: semantic reflexivity.

-- Source: $is_set(1)
Litex.IsSet (1 : ℂ)
-- Proof adapter: encodeComplex 1 is an actual model set.
```

The second proof may be elementary in a pure-set model, but its justification is the actual denotation `encodeComplex 1`, not the mere existence of a Lean type and not an unproved compiler axiom. Both facts retain their source FactIds. `1 $in R` and `1 $in C` then add separate propositions about the same unchanged `(1 : ℂ)` representative.

Standard sets are encoded ranges over that shared complex code. R membership exposes a real representative, and C membership exposes a complex representative. Their public contracts remain polymorphic in the original object's host type:

```lean
-- Proposed semantic contracts.
In a C ↔ ∃ z : ℂ, Same a z
In a R ↔ ∃ r : ℝ, Same a (r : ℂ)
```

R-to-C transport adds knowledge about `a`; it does not change `α`. Native complex membership in R can additionally eliminate to zero imaginary part. The exact native carriers of N/Z/Q/R are useful views for Mathlib and integer-specific operations, while emitted source numeric constants and intrinsic results still have the canonical complex representation.

For an arbitrary source identifier used in arithmetic, the current verifier already checks membership as a fact. The following exact source was accepted by the installed release binary:

```litex
have a R
a + 1 = a + 1
```

The target construction is schematically:

```lean
-- Proposed lowering; a : α remains unchanged.
let haC := Litex.in_C_of_in_R haR
let one := Litex.numeral 1
let sum := Litex.add a one haC hOneC
-- Core's proved bridge opens sum to the corresponding native addition.
```

The new `sum` is the representation of the compound expression; it is not a replacement binding for `a`. Core must prove that a numeric observation z satisfies `Same a z`, uniqueness of z, agreement between R and C views, and congruence of the numeric operation. Division also consumes the source nonzero proof and opens it into the native denominator condition. The [current Add WD](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs) retains child WD results and both `In(_, C)` requirements in `AddObjWellDefinedProof`, so the compiler can consume the verifier-selected facts instead of inferring a new source type.

All other construction families follow the same principle: choose a useful native representation, establish its one fixed pure-set meaning, prove the constructor/member/application laws, and expose native data only through checked facts. For sets, an exact presentation must cover precisely their members and count semantic duplicates once. For functions, graph identity retains complete domains and source application layers while ignoring return upper-bound labels. Tuples and empty functions share the ordinary empty-set identity when their graphs are empty. Source structs retain their definition-owned coordinate and law interfaces. This policy does not authorize representing unsupported constructions as opaque syntax containers and claiming semantic support.

The October 8 scalar baseline also accepted `1 = 1`, `$is_set(1)`, `1 $in R`, `1 $in C` and `1243 $in C`. The observed equality route was same-object reflexivity, sethood used AlwaysTrue after WD, and numeric memberships used closed calculation. Production interpretation metadata, canonical numeric lowering and the generic public bridges still need implementation and kernel validation.

## First MVP scope

The user's October 8 steering makes object introduction, sethood, membership and the R/C hierarchy the first compilation slice. A further correction fixes representation independence: a source object admitted by `a $in C` must remain a representative in arbitrary Lean host type `α`; the membership fact does not restrict its host type to `ℂ`. Reflexivity applies independently of C membership. The reciprocal example below is a later WD/application slice. The first MVP should support representation-independent identifiers, the standard domains `R` and `C`, ordinary typed `have`, atomic sethood/membership/equality, and the shallow single-conclusion universal needed to export the hierarchy law.

The following exact source passed the installed release binary with exit 0, `kind: run`, `success: true` and `session_error: null`:

```litex
have a C
$is_set(a)
a $in C
a = a
$is_set(R)
$is_set(C)
```

This second source also passed the same contract:

```litex
have b R
b $in R
b $in C
forall x R:
    x $in C
```

The actual `b $in C` route is structural membership through the standard superset relation and its stored R-membership source. It is not an eager inference result. Compiler support must consume that exact typed certificate and FactId. Known-membership replay, object reflexivity and the `IsSet` AlwaysTrue rule are the other initial atomic routes.

The negative source below returned exit 1 and `success: false` at its second statement, while `have z C` succeeded. This is failure to establish real membership, not proof of nonmembership:

<!-- litex:skip-test -->

```litex
have z C
z $in R
```

The public semantic interface is heterogeneous. Lean's host type supplies storage for a representative; Litex membership supplies mathematical classification. In particular, these are the revised target contracts, not implemented Core declarations:

```lean
-- Proposed public contracts, independent of a's host carrier.
Litex.In a Litex.C ↔ ∃ z : ℂ, Litex.Same a z
Litex.In a Litex.R ↔ ∃ r : ℝ, Litex.Same a r
```

Together with a proved `Same r (r : ℂ)` bridge, the R witness establishes C membership without changing the original `a : α`. The selected numeric representative must be unique in its faithful native carrier. `a`, `R` and `C` need actual pure-set interpretations, so the model justifies the source sethood rule; the target must retain the named proof for the source IsSetFact. A number's host Lean type alone is not a set-theoretic interpretation.

`have a C` checks C's nonemptiness, introduces a fresh source object, and stores its membership. Its exported context has `{α : Type u} (a : α) (haC : Litex.In a Litex.C)`. It must not silently restrict `α := ℂ`, fix `a := 0`, erase the context or add a project axiom. Core reflexivity does not need haC; the source context still registers that evidence under its FactId. The revised schematic theorem shapes are:

```lean
-- Intended context and theorem shape; Core names remain proposed.
theorem self {α : Type u} (a : α) :
    Litex.Same a a := Litex.Same.refl a

theorem real_to_complex {α : Type u} (x : α) (hxR : Litex.In x Litex.R) :
    Litex.In x Litex.C := Litex.in_C_of_in_R hxR
```

`Same` may relate endpoints of different host types. Native Lean equality implies Same. The converse needs a proved faithful observation, such as native complex endpoints; even identical endpoint host types do not justify general native equality. Proposed acceptance shapes include `Same (3 : ℕ) (3 : ℂ)` and two reviewed wrapper representatives `Sum.inl (3 : ℂ)` and `Sum.inr (3 : ℂ)` that are semantically Same while natively unequal. Reject `Same (3 : ℂ) (4 : ℂ)`. These wrapper examples are proposed controls, not executed proofs.

Fixed-domain membership must respect element equality. General source membership must also respect equality of the set argument. The compiler must not recover these laws by rendering source equalities as Lean casts. A native adapter opens `haC` to a complex representative and a Same certificate; it does not retype the original value. No numeric typeclass on arbitrary `α` should be an additional source-level prerequisite for using that membership fact.

The model-backed denotation proposal remains a possible backend, but it must establish this public contract. A total per-type `Representation` map implicitly required by `Same` is representation metadata that must be supplied coherently, not a new source premise. An alternative closed semantic relation can define membership by the representative witnesses above. Arbitrarily existentially choosing unrelated representation maps inside `Same` or `In` would collapse distinctions and is forbidden. Merely changing a theorem binder to `α` does not discharge coherence, uniqueness or sethood obligations. No backend is selected by this correction alone.

The exact declaration's original AST, source order, identifiers and FactIds still need capture. The minimal producer path is `HaveObjInNonemptySet` and its nonempty/membership outputs, followed by the four supported atomic proof routes and shallow forall introduction. Unsupported Result variants must produce an explicit diagnostic.

Acceptance must run the Litex source, compile the actual successful results, check the generated file in Lean, and use a proved adapter on that generated theorem. A native specialization supplies a known faithful host representation, then recovers its native equality. For an arbitrary `x : α`, real membership instead gives a real representative and a Same certificate; native casts to ℂ become available only for that selected representative. Test at least two host carriers and the same-carrier wrapper control to ensure the implementation preserves representation independence. Keep reverse-hierarchy, fresh-object-equals-zero and dead-FactId controls. Functions, arithmetic normalization, induction, general set construction and named foundational releases belong to later slices.

This is the proposed first implementation scope, not a completed compiler. The existing mathematical feasibility probe establishes model lemmas, and the October 8 CLI checks establish current source behavior; neither alone establishes the full end-to-end acceptance.

## A subsequent function source and its intended export

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

## Full pure-set correspondence: a candidate model backend

The old representation `Set { Carrier : Type }` and heterogeneous equality carry useful ideas, but they do not by themselves model all objects as sets. The current [set WD](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/sets.rs) checks only child WD for operations such as `power_set`. Thus an expression such as `power_set(1)` needs a mathematical interpretation under the existing contract, even though it is not a common numeric use case.

Giving each numeric value an empty membership extension would make all numbers equal by global extensionality. Adding an unconstrained bridge relation would instead make equality transport unsafe. The retained Core also distinguishes object equality from a separate `SetEquivalent`; the new model must establish both argument positions of membership congruence.

A candidate mathematical contract for the full pure-set extension is the following schema. It is one way to discharge coherence, not a required replacement for the retained public interfaces. These are proposed interfaces, not complete Lean declarations:

```lean
Representation α: a fixed map denoteα : α → ZFSet.{u}
Same x y := denoteα x = denoteβ y
In x A := denoteα x ∈ denoteβ A
```

Representation is selected explicitly by a declaration or construction. A later membership fact must not silently replace it. There is no blanket default instance asserting that every Lean type has a valid Litex interpretation. Different native views of an object share proved equal denotations.

This definition gives one semantic equality and proves symmetry, transitivity, membership transport on either side and extensionality from the underlying set model. Numeric observation laws become consequences of correspondence proofs. They do not define a second observer-indexed equality. Recover native `x = y` only when the specific representation is proved injective.

`ZFSet` is Mathlib's existing mathematical model, constructed as an extensional quotient of pre-sets. It supplies definitions and proved interfaces for powersets, images, well-founded membership and function graphs. It is a candidate semantic foundation, not an invented `axiom LitexObject : Type`. See the [Mathlib ZFC documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/ZFC/Basic.html). Its presence does not automatically prove the numeric and function correspondence needed here.

For unrestricted source `forall A set`, the public translation retains a generic representative A and an IsSet fact, with fixed interpretation metadata. A model-backed adapter can expose `A`'s `ZFSet` view. It must not force the public source-object binder to that host type or narrow it to a package of native element types. Sethood may reduce to an elementary proposition in a pure-set model, but only because every denoted value is actually a set; its source FactId remains bound to the corresponding proof. This is different from erasing sethood while leaving numeric and function objects uninterpreted as sets.

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

For this candidate model backend, choose and prove one injective complex encoding `encodeC : ℂ → ZFSet`. Define the other number representations through the native embeddings:

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

For one source layer, retain fixed parameter domains, guards, return bound and Litex-owned body/application operations. Combining native domains into an input product is allowed only in an external function adapter. Such an adapter may have the shape:

```lean
-- Optional external adapter view, not the internal function representation.
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

1. **Specify the objects and their semantics.** Keep native numeric values, heterogeneous Same/In and generic source parameters. Use Litex-owned representations and operations for the other object families, including FnSet, function values, FnObj applications and images. Native presentations are secondary adapters. Use the new equality-class semantics; do not preserve the old proof pipeline as an implementation requirement.
2. **Implement the supported object contracts.** Establish genuine sethood, equality/membership laws and the native views needed by the first consumer. Retained reflexivity and R-to-C mathematics can be reused without preserving their historical evidence route. No project axioms or proof holes. The larger graph/foundation extension is not a prerequisite for the initial slice.
3. **Complete the initial evidence path.** Preserve source declarations, generic binders, exact membership and sethood FactIds, scope ownership and original statement capture. Compile the minimal have/reflexivity/R-to-C sources from actual successful Results.
4. **Check the initial export, then extend to arithmetic and reciprocal.** Run the generated Lean and a native consumer. Add a same-name source/generated pair only after all stages work. Subsequently complete guarded application, function coherence and the reciprocal path; test valid and missing-guard cases. A handwritten adapter consumes the generated proof without reproving the mathematical goal.
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

## Remaining later-slice questions

**Generation architecture is settled for the baseline.** The user's latest direction keeps the retained native representations. All-model generation remains background analysis, not a pending choice or a reason to delay the initial slice. The internal method for proving full pure-set correspondence still requires mathematical work.

**Numeric interiors.** An implementation-fixed complex set encoding can remain outside the public source rules while supporting native arithmetic. Alternatively, publish the von Neumann natural-number convention, including `0 = {}` and `0 $in 1`, and require every larger numeric domain to reuse those same objects. Neither convention follows merely from the current `AlwaysTrue` sethood rule. Publishing a convention increases future compatibility obligations.

**Empty absolute family intersection.** Current WD accepts the child-only form:

<!-- litex:skip-test -->

```litex
# Illustrative boundary; not run here.
family_intersect({})
```

However, current intersection membership rules require nonempty families, and one equality-rule comment describes empty absolute intersection as a universe class. A universal class cannot be an internal set in this model. Choose either a nonempty-family WD requirement or an explicit totalized set value, such as the empty set with suitably restricted laws. This is an unsettled denotation contract, not a demonstrated soundness failure. Keep it unsupported in the compiler until the source decision is fixed. Existing `index_intersect(I, X, A)` has an explicit ambient set and separate obligations; it does not silently settle this absolute operator's meaning.

The immediate implementation scope is the minimal object/reflexivity/sethood/R-to-C slice above, retaining native representations. Prove its exact missing contracts and reconnect it to current Results before expanding to reciprocal or foundational rules. A passing partial slice must not be described as support for the entire pure-set system.
