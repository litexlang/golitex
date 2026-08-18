# Compiler examples

This directory is the canonical generated ledger for examples targeting the
`litex_to_lean_compiler` ABI. Every example has one authoritative `.lit`
source and one same-name generated `.lean` output. It must not import or depend
on the archived universal-`Litex.Object` ABI.

Every generated file imports the public `Litex` umbrella module. The umbrella
owns the internal module list, so adding supported theorem or strategy modules
does not require changing the generated import header.

Refresh every pair from fresh Litex verification and verifier-owned IR:

```sh
cd lean
./compiler.sh generate examples
```

After editing one source, refresh only its same-name output:

```sh
cd lean
./compiler.sh compile examples/1_SetSystem.lit
```

Check byte-for-byte freshness and run every output through Lean:

```sh
cd lean
./compiler.sh check examples
```

Compiler preserves source sketch scope. A top-level `sketch:` becomes an
isolated `__SketchNN` namespace nested inside the file namespace; declarations
and FactIds created there do not become later file-level bindings. Ordinary
top-level facts are emitted directly in the file namespace.

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
`Litex.In` premise. The paired negative regression uses verified `N+ → N` and
requires compiler to reject it until the refined exact-carrier ABI exists.

Generated `.lean` files are review artifacts, not editing surfaces. A new
compiler feature must add the next numbered same-name pair. Unsupported
statements, objects, facts, or proof routes fail closed.
