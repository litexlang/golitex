# To-Lean Translation Model

## Honest partial compilation

Compiler completeness is part of the semantic return value, not merely prose
printed beside generated code. The report interface is:

```text
ToLeanCompilationReport {
    lean_code: checked supported subset,
    status: Complete | Incomplete,
    unsupported: [statement index, source location, phase, reason],
}
```

This separation matters because Litex verification and Lean lowering answer
different questions. A verified statement such as `sin(0) = 0` can be valid
Litex mathematics while its selected builtin proof route has no compiler
certificate. That is not a source verification failure, and it must not become
an unchecked Lean theorem. Report mode records it as unsupported, leaves a
comment at its source position, and continues with later independent IR.

One statement is the transaction boundary. Before emitting it, the backend
copies all declaration and naming state. Failure in any nested proof rolls the
copy back, so a multi-fact statement cannot leak an earlier axiom, theorem, or
reserved `FactId`. This boundary is narrower than the whole file and wider than
an individual proof node.

The nearest rejected behavior is treating parse failure or an unverified Litex
goal as partial compiler success. Those remain hard errors because no checked
source statement exists to omit. A later statement that depends on an omitted
declaration is attempted normally and receives its own explicit unsupported
diagnostic if that dependency cannot be materialized.

## Statement effects and proof scopes

A source statement can change more than the fact cache. It may create a named
object, open a temporary assumption scope, run nested statements, and export
one or more facts only after the scope closes. Compiling these forms therefore
requires a statement-effect IR beside the recursive proof IR; flattening every
successful result to a global theorem loses both declaration order and premise
lifetime.

The current mapping is:

| Litex form | Required semantic evidence | Lean shape |
| --- | --- | --- |
| `have x T = e` | symbol identity, canonical value, checked `e T`, stored type/equality `FactId`s | top-level `def`, or local `let`, then checked facts |
| `have x S` | symbol identity, checked nonemptiness producer, exact stored membership `FactId` | top-level `noncomputable def`, or local `let`, via `Exists.choose`; membership via `choose_spec` |
| `witness exist ... from ...` | concrete witnesses, pre-binder type proofs, scoped proof steps, checked direct body facts | nested `Exists` introduction from the retained proof nodes |
| `obtain ... from exist ...` / `have x T: ...` | alpha-checked source existential, fresh symbol identities, instantiated type/body facts and `FactId`s | ordered nested `Exists.choose`; exact `choose_spec` projections |
| `by cases` | coverage proof, ordered local premise IDs, nested steps, conclusion/contradiction exits | coverage `have`; `rcases`; scoped branches |
| `by contra` | target, logical reverse premise ID, nested steps, final fact/negation pair | scoped `Classical.byContradiction` |

An explicit-value `have` is a definition, not existential choice. Its initial
IR is:

```text
HaveObjEqual {
    definitions: [{ symbol_id, name, param_type, value }],
    facts: [value-in-type, defining-equality],
}
```

The backend validates those facts against the declaration contract. It checks
the value's type before unfolding the new name, proves the corresponding named
membership with `simpa only [name]`, and proves the defining equality by
reflexivity. Top-level declarations use `def`; the same node nested in a proof
uses `let`, so its symbol cannot escape the proof scope.

The nearby syntax `have x S` has different semantics. It selects an element
from a known nonempty carrier. Runtime therefore returns, in declaration order,
the exact stored type fact for every new object and the index of the retained
nonemptiness proof that produced it. The supported compiler IR freezes that
contract as:

```text
HaveObjChoice {
    choices: [{
        symbol_id,
        name,
        carrier,
        nonempty_proof,
        membership: FactProof { fact_id, ObjectChoice },
    }],
}
```

The target definition
`litexIsNonemptySet S := Set.Nonempty S` makes the verification fact itself
the choice package. At file scope the emitter names that checked theorem,
defines `x` with `Exists.choose`, and proves the stored membership with
`Exists.choose_spec` from the same theorem. In a proof scope those three values
remain local. The emitter independently validates the proof's carrier, the
selected `SymbolId`, the membership carrier, and the stored `FactId`; missing or
mismatched fields reject the whole statement transactionally.

Positive existential introduction and elimination use a wider package than
bare selection. The introduction proof rule retains:

```text
ExistIntroduction {
    witnesses,
    steps,
    expected_parameter_requirements,
    expected_body_facts,
}
```

Concrete witness-type checks are captured before the verifier installs its
temporary existential parameters and equalities. Otherwise a valid-looking
proof of `e $in T` could cite binder-local facts that disappear when that
environment is popped. Plain `set` parameters need no target proposition
because the target binder itself has type `Set α`; object,
`nonempty_set`, and `finite_set` parameters retain their separate requirements.
The emitter replays the local steps, names the retained proofs, and builds the
nested existential package with its concrete witnesses. Closed numeric binary
facts receive one justified fact-level native expectation when inference would
otherwise default to the wrong numeric carrier.

Elimination freezes the result as:

```text
HaveExistentialWitness {
    source: FactProof,
    witnesses: [{ symbol_id, name, instantiated_param_type }],
    projections: [
        { fact_id, ParameterType { witness_index }, expected_fact },
        { fact_id, BodyFact { body_index }, expected_fact },
    ],
}
```

The source must be a checked positive existential. Litex stores existential
facts modulo alpha-renaming, so a citation with fresh binder `SymbolId`s is not
ordinary display-string equality: runtime lowering emits an explicit
alpha-renaming citation only after the verifier's canonical existential body
comparison succeeds. At file scope the emitter names the source proof and
defines witnesses with ordered, nested `Exists.choose`; inside a proof the same
objects are local `let`s. Every stored parameter/body fact is proved by the
corresponding `Exists.choose_spec` path. The emitter checks source, role order,
selected symbol, instantiated type family, expected proposition, and distinct
`FactId`s before emitting any part of the statement.

Quantifier rendering retains one further identity guard. Binder declarations
and every object occurrence are compared by `SymbolId` and by their sanitized
Lean spellings. A binder occurrence with a mismatched spelling, or two
different symbols that would both print as the same Lean identifier, is an
explicit incomplete boundary; the backend never emits a captured formula.

The implemented builtin nonemptiness backend currently covers the native real
universal set.
A stored nonemptiness theorem can also be cited when its own proof route is
supported. Meta-level parameter types (`set`, `nonempty_set`, `finite_set`) and
object carriers whose proof/object lowering is unavailable remain explicit
boundaries. This form does not reuse `HaveObjEqual` with an invented value,
emit an unconstrained `opaque`, or introduce a silent axiom. Positive
`witness exist`, `obtain`, and body-style existential `have` now use the
separate package above. `exist!`, `not exist`, preimage selection, and
uniqueness-based function construction still need distinct evidence contracts.

Function definitions do not yet have a frozen native target contract.
`have fn ... = ...`, case-by-case definitions, recursive definitions, and
unique-existence definitions need a typed function-object declaration plus
application/evaluation laws. Until that interface is modeled, the compiler
fails closed rather than restoring the retired universal value wrapper.

Case analysis has the following proof contract:

```text
CaseSplit {
    coverage: FactProof,
    branches: [
        {
            assumption: LocalPremise { fact_id, fact },
            steps: [StmtToLeanIR],
            exit: Conclusion(FactProof)
                | Contradiction { fact, negated_fact },
        },
    ],
}
```

Coverage is proved outside the branches. Each branch then receives a fresh
proof-space name for exactly its retained temporary `FactId`; nested statements
may cite that ID but sibling and parent scopes may not. A contradiction exit
first checks both propositions are logical complements, materializes their
proofs in the branch, derives `False`, and eliminates it to the requested goal.
The implemented coverage slice is binary complementary atomic facts, lowered
through classical excluded middle. General finite covers need a typed coverage
certificate rather than a broader tactic call.

Contradiction has a similar but single-scope contract:

```text
ByContradiction {
    reverse_assumption: LocalPremise { fact_id, fact },
    steps: [StmtToLeanIR],
    contradiction: { fact, negated_fact },
}
```

The source verifier's logical reversal is retained before its temporary
environment is popped. The Lean emitter validates that reversal against the
target, introduces it only under `Classical.byContradiction`, emits the local
steps, and checks the final complementary pair. The first implementation is
intentionally atomic; quantified or binder-owning targets need their own
introduction IR rather than being reconstructed from display syntax.

The dependency order for wider statement coverage is:

```text
explicit-value have [implemented]
  -> selection have [implemented for checked object carriers]
  -> positive existential introduction/elimination [implemented]
  -> theorem and definition proof wrappers
  -> function-object declaration plus evaluation evidence
  -> function-range preimage have
  -> induction and finite enumeration scopes
  -> extension and specialized relation/choice proof commands
```

Each new family must preserve its successful temporary premises, nested
statement results, exported facts, and exit condition before a Lean backend is
added. A verified family missing any of those pieces remains an explicit
incomplete statement; it never falls back to `sorry` or a compiler-created
axiom.

## Recursive builtin-rule application

A successful builtin rule is a proof-tree node, not just a message saying that
some automation succeeded. Its mathematical content consists of a stable rule
identity, the objects bound by the rule's target pattern, any target
orientation, and recursively checked premises. This distinction matters after
the Litex verifier scope has returned: a compiler must reconstruct the selected
derivation without running the matcher or proof search again.

The implemented interface has two typed layers:

```text
BuiltinRuleEvidence
  + Vec<StmtResult> child proofs
  -> BuiltinRuleToLeanIR
  + Vec<FactToLeanIR> recursive premises
  -> validated Lean child terms
  -> Lean lemma application for the parent rule
```

`VerifiedByBuiltinRuleResult` owns the first pair. Its evidence and children
remain paired even when a result is wrapped by statement memoization or merged
into a `VerifiedBys` sequence. `FactProofToLeanIR::RuleApplication` owns the
second pair. This node is recursively compositional: a premise may itself be a
citation, normalization, known-forall application, another supported builtin,
or any later proof rule with a checked backend.

The IR's recursive shape is independent of proof-search depth. Litex's current
one-builtin-rule budget remains authoritative; recording and replaying the
selected tree does not authorize another automatic rule application.

The representative signature is quotient nonzero:

```text
DivNotEqualZero {
    numerator: Obj,
    denominator: Obj,
    orientation: ExpressionOnLeft | ExpressionOnRight,
}
premises = [numerator != 0, denominator != 0]
```

For `a / b != 0`, Lean checks `div_ne_zero ha hb`; for `0 != a / b`, it checks
`Ne.symm (div_ne_zero ha hb)`. Before emitting either term, the backend checks
that the recorded bindings match the target quotient, that the zero is
literal, and that the two recursive premises have the expected propositions.
This validation makes malformed IR a compilation error rather than an invalid
theorem or an implicit trust boundary.

The nearest rejected form is `a / b != z` when Litex resolved `z` to zero from
its environment. The verifier can prove it, but the current builtin evidence
does not carry the equality path from `z` to `0`. Supporting that target should
compose explicit equality-transport evidence around the direct builtin
instance; it must not broaden the quotient rule to erase that missing proof.
Other label-only builtin rules likewise remain `OtherUnsupported` until their
complete bindings and premise contract have a typed evidence variant and a
checked Lean backend.

The first broader tranche uses `ArithmeticBuiltinRule`, a stable 20-case rule
identity whose complete certificate is the target plus an ordered list of
recursively checked premises. Lowering validates each target and premise as an
equality, weak-order, or strict-order fact before producing any theorem. The
16 linear rules use `linarith only` with exactly those named premise proofs;
the four nonlinear sign rules use `mul_nonneg`, `mul_pos`, `div_nonneg` (with
`le_of_lt` for the positive denominator), and `div_pos`. This keeps proof
search out of the certificate boundary: a malformed rule ID, target family,
premise family, or arity fails compilation instead of widening automation.

A builtin strategy may now use the same certificate path without pretending
that its diagnostic label is a theorem. The result retains both identities:

```text
BuiltinStrategy {
    strategy_label: diagnostic search provenance,
    evidence: Some(BuiltinRuleEvidence),
    steps: recursive child proofs,
}
  -> RuleApplication {
       rule: Builtin(BuiltinRuleToLeanIR),
       premises: recursive FactToLeanIR children,
     }
```

The evidence is attached only after an exact structural check of target,
operand order, strictness, and every child proposition. For the persistent
tracer this gives the following certificate tree:

```text
0 < (a + b) + (c + d)              AddPositiveLeftStrict
├── 0 < a + b                      AddPositive
│   ├── 0 < a                      cited R+ consequence
│   └── 0 < b                      cited R+ consequence
└── 0 <= c + d                     AddNonnegative
    ├── 0 <= c                     LessEqualFromStrictOrder <- 0 < c
    └── 0 <= d                     LessEqualFromStrictOrder <- 0 < d
```

Each parent is emitted only after its children. Mutating the root to
`AddPositiveRightStrict`, for example, fails the strict/weak premise contract
before Lean source is accepted. A non-additive structural route such as
`x^2 < y^2 -> abs(x) < abs(y)` remains deliberately label-only and therefore
explicitly unsupported by the compiler.

## Known-forall instantiation

A successful use of a known forall retains four distinct pieces of evidence:

```text
recorded Obj arguments
  -> typed local proof_arg values
  -> recursively proved domain requirements
  -> direct instantiated conclusion
  -> optional checked normalization to the requested goal
```

The parameter-type requirements remain explicit in IR. Lean realizes each one
by type-checking a local definition such as `let proof_arg_2_1 : ℝ := e`; this
is the Lean evidence that the chosen Litex object inhabits the translated
forall binder type. Proposition-valued domain requirements instead become
named `proof_fact` values and are supplied to the cited theorem after the
`proof_arg` values.

The direct conclusion is instantiated from the exact recorded objects. It is
not replaced with the requested goal merely because Litex's matcher accepted
the two. For the current atomic rational slice, a different but rationally
equivalent target is represented by an outer `Normalization` rule. This gives
the inner forall application its own proof space and leaves the outer proof to
check the conversion with `norm_num`, `ring`, or `field_simp` plus `ring`.

The nearest boundary is a direct instance and goal that need some other form of
transport, or a recursively verified domain requirement whose proof rule has no
Lean backend. Both remain explicit unsupported nodes and stop compilation.

## Resolved atomic-fact transformations

Known atomic-fact lookup may normalize objects before it finds a stored
proposition. That search is goal-to-source, whereas a proof term must be built
source-to-goal. Returning only the final citation loses precisely the middle
derivation that Lean needs. The verifier therefore retains:

```text
FactTransformationEvidence {
    source: stored proposition reached by resolution,
    steps: [
        { result, RationalNormalization },
        { result, EqualityRewrite { oriented equality edges + FactIds } },
        ...
    ],
}
```

The first implemented route for `a = 13`, `b = 1`, and known `$p(14)` is:

```text
$p(14)
  -> RationalNormalization -> $p(13 + 1)
  -> EqualityRewrite       -> $p(a + b)
```

The intermediate `$p(13 + 1)` is intentional. It separates a closed rational
calculation, discharged by the checked normalization backend, from the two
stored equalities used by `simpa only`. `resolve_obj` remains proof search and
does not become an opaque target tactic.

Substitution is keyed by the symbol's `SymbolId` and applied recursively to the
whole predicate argument object, rather than only to its top-level children.
Consequently the evidence builder also records:

```text
$p(f(14), c)
  -> RationalNormalization -> $p(f(13 + 1), c)
  -> EqualityRewrite       -> $p(f(a + b), c)
```

The equality side is recursive as well. It asks for a stored proof path between
the complete pair of subobjects before descending through the central
same-shape matcher. A compound premise therefore stays a single explicit
rewrite even below a function application:

```text
a + b = 14, $p(f(14), c)
  -> EqualityRewrite(14 -> a + b) -> $p(f(a + b), c)
```

This is structural congruence at arbitrary supported depth, not a claim that
all calls to `resolve_obj` are proof rules. A reduction which is not justified
by a stored equality or the checked rational normalizer must acquire its own
`FactTransformationRule` before To-Lean can replay it.

This recursive evidence is independent of target object coverage. The current
To-Lean object ABI rejects general `FnSet`/`FnObj`, so the second chain is a
verified verifier-result regression but not yet an emitted Lean theorem. Adding
function-object declaration and evaluation evidence is the prerequisite for
crossing that boundary; the compiler must not flatten the chain in the meantime.

## Forall-introduction inferred premises

Parameter membership facts and their immediate verifier inferences share one
temporary Litex environment. `ForallIntroduction` therefore owns two ordered
collections: the explicit binder premises and the supported inferred premises.
Each inferred fact records its `FactId` while that environment is still alive;
lowering must never try to rediscover the ID after the scope has been popped.

The first supported inference certificate is:

```text
a ∈ R+
  -> PositiveRealMembership { element: a }
  -> 0 < a
```

Its recursive premise is the exact binder-membership citation. Lean interprets
`R+` as `{r : ℝ | 0 < r}`, so the positivity result follows definitionally from
that native membership proof. An unsupported inferred consequence is not
silently emitted; if a selected proof depends on it, the enclosing statement
remains incomplete.

## Recursive fraction pair

The experiment maps a supported real expression `e` to a pair `(p, q)` meaning
`e = p / q`. This pair is structural rather than a human-minimal printed form.
Lean performs the final polynomial normalization and equality check.

Representative rules:

```text
atom a       -> (a, 1)
u + v        -> (pu * qv + pv * qu, qu * qv)
u - v        -> (pu * qv - pv * qu, qu * qv)
u * v        -> (pu * pv, qu * qv)
u / v        -> (pu * qv, qu * pv)
u ^ n        -> (pu ^ n, qu ^ n) for literal n in N
```

This matters because one recursive walk both renders the original Lean
expression and exposes whether denominator clearing is required. Polynomial
equalities use `ring`; remaining denominators use `field_simp` with the
translated explicit nonzero premises and then `ring`.

## Chained division

Division is left-associative in the Litex parser. Consequently,
`1 / 2 / 3 / 4` reaches this model as `(((1 / 2) / 3) / 4)`, and the recursive
rule accumulates the pair `(1, (2 * 3) * 4)`. This is intentionally a structural
normal form rather than a reduced numeric fraction. For a closed numeric
equality such as `1 / 2 / 3 / 4 = 1 / 24`, Lean's `norm_num` checks that the
two recursively built forms denote the same real number.

## Rational-expression boundary

The ideal later interface could normalize numerator and denominator polynomials
inside Litex and carry proof evidence for every denominator. This experiment
does neither. Its nearest rejected forms are a nonliteral exponent, a
non-rational object such as `sin(x)`, or a denominator whose nonzero evidence is
only implicit rather than an explicit universal premise.

## Numeric object ABI

This section freezes the replacement for the former one-carrier `LitexSet`
experiment. Litex has one `Obj` syntax and one source-level object identity, but
the target is allowed to give an occurrence the native type required by its
checked judgment. Source uniformity does not require a monomorphic Lean value
carrier.

`N`, `Z`, `Q`, `R`, and `C` are ordinary Litex set objects. A declaration such
as `z Z` still contributes the fact `z $in Z`; it is not source syntax for a
different object category. In Lean, however, that checked membership supplies
the faithful native interpretation `z : ℤ`. Proof provenance and target
elaboration are separate: `trust z $in Z` may introduce the proposition as an
axiom, but `trust` never chooses or changes `z`'s target type.

### Uniform object rendering

The canonical object tree remains structural and context-free:

```text
lower_obj(obj) -> ObjToLeanIR

Symbol(z)      -> z
Number(2)      -> 2
Div(z, 2)      -> z / 2
Add(q, 1)      -> q + 1
StandardSet(Q) -> Q
```

`ObjToLeanIR` preserves the source constructor tree, normalized number
spelling, and `SymbolId`. A separate checked target context records the native
carrier expected by a binder or fact. Plain object lowering does not attach a
temporary annotation such as `(z : ℝ)` and does not turn a numeral into a pair
of value and type.

This gives symbols, literals, and compound objects one stable spelling across
definitions, facts, proof certificates, equality transport, and `FactId`
citations. Target coercions are elaboration nodes justified at a judgment
boundary; they do not create another Litex object or change its `SymbolId`.

### Object universe and membership

Litex's object/fact distinction remains authoritative:

- every source `Obj` satisfies `$is_set(obj)`;
- a `Fact` or proposition is not an `Obj` and cannot be passed where an object
  is required;
- this source invariant does not imply that every target term has one Lean
  type.

The target uses a small polymorphic marker for that invariant and native
Mathlib carriers for standard domains. Its intended interface is equivalent to:

```text
LitexObject α : Prop
litexIsSet : [LitexObject α] -> α -> Prop

N -> (Set.univ : Set ℕ)
Z -> (Set.univ : Set ℤ)
Q -> (Set.univ : Set ℚ)
R -> (Set.univ : Set ℝ)
C -> (Set.univ : Set ℂ)
```

`LitexObject` has instances only for supported object carriers; it is not a
blanket instance for every Lean type. The frontend IR continues to enforce the
stronger source distinction, so this marker is an emitted proposition rather
than an attempt to reimplement the parser's object sort in Lean.

Standard-domain membership is a genuine proposition using Mathlib's native
membership relation:

```text
2 $in R

->

2 ∈ (Set.univ : Set ℝ)
```

The proposition itself both elaborates the bare numeral as `ℝ` and remains
available as a hypothesis, theorem, or trusted fact. It must not be erased as
mere typing metadata. Equality and the supported arithmetic operators likewise
use native `=`, `+`, `-`, `*`, and `/`; the target must not introduce wrappers
such as `LitexAddEq` or a private equality relation.

### Binders preserve bounded membership

A standard-domain binder is emitted in bounded-quantifier form:

```text
forall x R:
    P(x)

->

∀ x ∈ (Set.univ : Set ℝ), P x
```

Lean elaborates this as a native `x : ℝ` binder followed by a separate
membership premise. The generated surface does not need to print `(x : ℝ)`,
but the elaborated term is typed because `Membership.mem` fixes the element
carrier. The membership premise receives its own proof name and `FactId`
mapping just like any other Litex fact.

Refined standard sets are native predicates over their base carrier, for
example `{n : ℕ | 0 < n}` and `{z : ℤ | z ≠ 0}`. They remain membership
propositions, not Lean subtypes substituted for the source symbol.

A generic source set binder uses an implicit carrier:

```text
forall A, B set:
    ...

->

∀ {α : Type u} (A B : Set α), ...
```

The first tranche shares one implicit carrier among connected generic-set
binders in a declaration. Membership in such a set infers the element type from
the set. Native `A ∪ B`, `A ∩ B`, and `A \ B` are supported when their carriers
unify. Heterogeneous or otherwise underconstrained set expressions fail closed
until the IR can retain a sound carrier constraint; they do not fall back to a
universal wrapper.

### Numerals obtain constraints from facts, not annotations

A `Number` node lowers to its normalized spelling and nothing else. For
example, the object in `1 $in R` is emitted as `1`, and the containing
membership proposition supplies the native expectation:

```text
1 ∈ (Set.univ : Set ℝ)
```

It is not emitted as `(1 : ℝ)`. Likewise, `q + 1` keeps the bare literal `1`.
An unconstrained reflexive fact such as `1 = 1` also remains `1 = 1`; the
compiler does not invent a persistent `ℚ` or `ℝ` annotation merely because the
object is numeric. A closed arithmetic fact whose meaning depends on a carrier,
such as one containing division, needs one fact-level target carrier chosen
from checked verifier evidence. For example, the rational-expression
normalization certificate selects `ℚ` for its closed judgment. The carrier is
not stored on each numeral. If the compiler cannot justify one carrier, it must
report the fact as unsupported instead of silently treating division as `Nat`.

### Canonical coercions are judgment-level evidence

Mathlib has the canonical tower `ℕ -> ℤ -> ℚ -> ℝ -> ℂ`, but Lean does not in
general propagate the right-hand set's element type backward through infix
membership after the left expression already contains a fixed-typed symbol. A
real Lean probe establishes the boundary:

```text
z : ℤ
z / 2 ∈ (Set.univ : Set ℚ)       -- does not elaborate
(z / 2 : ℚ) ∈ (Set.univ : Set ℚ) -- elaborates as (z : ℚ) / 2
```

Therefore the tracer

```text
forall z Z:
    z / 2 $in Q
```

is emitted with a target expectation on the whole compound object when needed:

```text
∀ z ∈ (Set.univ : Set ℤ),
  (z / 2 : ℚ) ∈ (Set.univ : Set ℚ)
```

The source object is still rendered structurally as `z / 2`; there is no
persistent `(z : Q)` annotation in `ObjToLeanIR`. Lean inserts the canonical
coercion in the elaborated term. The compiler may emit such a contextual
expectation only for a supported, directed coercion in the standard numeric
tower. Downcasts, ambiguous joins, and incompatible already-fixed carriers are
explicit unsupported boundaries.

In particular, `trust x $in R` can constrain a fresh source object whose
carrier has not otherwise been fixed, because the proposition must elaborate.
It cannot retroactively change an existing `x : ℤ` or narrow a generic set
carrier. `trust` decides only whether the completed proposition is an axiom.
Consequently, an underconstrained statement such as
`trust 1 / 2 = 1 / 2` is rejected by To-Lean: trust supplies proof provenance,
not the missing choice between natural and rational division.

### IR boundary

The target-aware IR is split deliberately:

```text
ObjToLeanIR =
    Symbol { symbol_id, name }
  | Number { normalized_value }
  | BuiltinApp { operator, ordered_args }
  | StandardSet { identity }
  | Collection { constructor, ordered_items }

LeanCarrierToLeanIR =
    Natural | Integer | Rational | Real | Complex
  | Generic { constraint identity }
  | Set { element carrier }

ParamTypeToLeanIR =
    Set { element carrier }
  | MemberOf { set, element carrier }
  | NonemptySet { element carrier }
  | FiniteSet { element carrier }
```

`ObjToLeanIR` owns identity and spelling. Carrier constraints belong to
binders, facts, and applications. The emitter solves those checked constraints,
renders standard sets as native `Set` expressions, and inserts only canonical
coercions justified by the solved source/target pair.

The existing raw `Obj` and `Fact` values may remain attached for diagnostics.
An unsupported object constructor, unresolved carrier, set representation, or
operation law makes report mode `Incomplete` and strict mode fail. It must not
trigger a fallback to `ℝ`, `Nat`, or the retired monomorphic carrier.

### Implementation dependency order

```text
structural ObjToLeanIR
  -> explicit carrier constraints in binder/fact IR
  -> polymorphic LitexObject marker
  -> native standard sets and bounded membership
  -> native equality, order, and arithmetic
  -> canonical numeric coercion insertion
  -> native generic set operations
  -> normalization and builtin-rule lowering over native terms
  -> additional Obj families
```

The first migration tranche covers `N`, `Z`, `Q`, `R`, `C`, their refined
subsets, bare numerals, `+ - * /`, equality/order, standard and generic
membership, and `union`, `intersect`, and `set_minus` on one unified element
carrier. `SetBuilder`, heterogeneous collections, unsupported transcendental or
complex operators, and coercions outside the canonical tower remain explicit
boundaries until their native Mathlib contracts are modeled.

The numeric source tracer is
[`to_lean_numeric_obj_abi.lit`](../../examples/05_compiler_interop/to_lean_numeric_obj_abi.lit).
It fixes native bounded binders, the unchanged source spelling of `z / 2`, the
required contextual `ℤ -> ℚ` coercion, native equality, and bare numeral
membership. The
implemented structural set-object tracer is
[`to_lean_set_obj_abi.lit`](../../examples/05_compiler_interop/to_lean_set_obj_abi.lit);
it is the migration target for native `union`, `intersect`, and `set_minus`,
plus the binder-aware `SetBuilder` rejection boundary.
