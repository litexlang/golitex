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
`litexIsNonemptySet S := ∃ x, litexMem x S` makes the verification fact itself
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
because every target value already has type `LitexSet`; object,
`nonempty_set`, and `finite_set` parameters retain their separate requirements.
The emitter replays the local steps, names the retained proofs, and builds the
nested existential package with its concrete witnesses. Closed numeric binary
facts receive a `LitexSet` ascription when inference would otherwise default to
a native Lean numeric type.

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

The implemented builtin nonemptiness backend currently covers the real carrier.
A stored nonemptiness theorem can also be cited when its own proof route is
supported. Meta-level parameter types (`set`, `nonempty_set`, `finite_set`) and
object carriers whose proof/object lowering is unavailable remain explicit
boundaries. This form does not reuse `HaveObjEqual` with an invented value,
emit an unconstrained `opaque`, or introduce a silent axiom. Positive
`witness exist`, `obtain`, and body-style existential `have` now use the
separate package above. `exist!`, `not exist`, preimage selection, and
uniqueness-based function construction still need distinct evidence contracts.

Function definitions are also not native Lean function declarations at the
canonical object boundary. A Litex function is a `LitexSet` graph object.
`have fn ... = ...`, case-by-case definitions, recursive definitions, and
unique-existence definitions need a function-object declaration plus typed
application/evaluation laws. A backend may use a native function only as a
local proof view justified by that evidence; it may not replace the canonical
object in emitted statements.

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

Its recursive premise is the exact binder-membership citation. Lean first
interprets `R+` membership semantically as positive real membership, then
checks `litexMemRPosPositive`. The companion `litexMemRPosReal` lemma supplies
the native-real proof view used by arithmetic emission without changing the
canonical `LitexSet` object. An unsupported inferred consequence is not
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

This section freezes the source-facing object interface before the compiler
adds more proof-rule backends. Litex has one `Obj` syntax. `N`, `Z`, `Q`, `R`,
and `C` are standard-set objects, and a declaration such as `z Z` contributes
the fact `z $in Z`; it does not change `z` into a different kind of object.

The former real-only emitter assigned native real annotations while proving
some arithmetic facts. That representation is not the object ABI: native
numeric values now occur only behind a checked proof view.

### Uniform object rendering

The canonical object lowering is structural and context-free:

```text
lower_obj(obj) -> ObjToLeanIR

Symbol(z)      -> z
Number(2)      -> 2
Div(z, 2)      -> z / 2
Add(q, 1)      -> q + 1
StandardSet(Q) -> litexQ
```

`ObjToLeanIR` preserves the source constructor tree, normalized number
spelling, and `SymbolId`. It contains no inferred `Natural`, `Integer`,
`Rational`, `Real`, or `Complex` carrier and no numeric coercion node. In
particular, object lowering must never turn `z / 2` into an expression such as
`(z : ℚ) / (2 : ℚ)`.

This gives symbols, literals, and compound objects one stable spelling across
definitions, facts, proof certificates, equality transport, and `FactId`
citations. A proof may learn additional memberships about an object without
changing the object that those facts mention.

### Object universe and membership

The Lean target has one carrier because every Litex object is a set. `LitexObj`
is not a second semantic type; if that historical name appears in Rust, it is
only an alias for the same carrier. The fixed target interface is:

```text
LitexSet : Type
litexN, litexZ, litexQ, litexR, litexC : LitexSet
membership : LitexSet -> LitexSet -> Prop
```

Thus the semantic shape of the tracer is:

```text
forall z Z:
    z / 2 $in Q

->

forall z LitexSet:
    z $in litexZ
    =>:
        z / 2 $in litexQ
```

The target binder's single `LitexSet` annotation is global compiler scaffolding;
it is not a temporary claim that `z` is a Lean integer, rational, or real.
Every occurrence in the translated object remains the bare symbol `z`.

`LitexSet : Type` is the meta-level carrier of set-values. It is not a Litex
universal-set object, and the target must not define it recursively as
`Set LitexSet`. Facts remain `Prop`. Function objects are `LitexSet` graph
objects too; a later application primitive may expose a local native function
view for proofs, but a native Lean function is not their canonical value.

A source binder `A set` therefore becomes only `(A : LitexSet)`. A source
binder `z Z` becomes `(z : LitexSet)` followed by the proposition
`z ∈ litexZ`. The membership is proof data, not a different binder type.

Standard-set inclusion is likewise preserved as mathematics about objects:

```text
litexN subset litexZ subset litexQ subset litexR subset litexC
```

Refined sets such as `N+`, `Z*`, and `Q-` remain set values or membership
predicates. They are not Lean subtypes attached to each symbol.

### Numerals obtain constraints from facts, not annotations

A `Number` node lowers to its normalized spelling and nothing else. For
example, the object in `1 $in R` is emitted as `1`, and the containing
membership proposition supplies the `LitexSet` expectation:

```text
1 $in litexR
```

It is not emitted as `(1 : ℝ)`. Likewise, `q + 1` keeps the bare literal `1`.
Closed equality and order facts must use monomorphic Litex fact interfaces, or
another enclosing `LitexSet` expectation, so Lean never needs to default an
otherwise unconstrained numeral to `Nat`. That constraint belongs to the
monomorphic `LitexSet` operations and fact lowering, not to local carrier
inference in `Obj` lowering.

This separation is important because a Litex numeral may have many true
memberships. Prematurely assigning `1` to `Z`, `Q`, or `R` would manufacture
different target terms for one source object and could select the wrong target
operator, such as integer division.

### Operators stay attached to the object universe

Each Litex operator has one target operation on `LitexSet`. The verifier's
well-definedness and membership evidence controls where that operation may be
used and what standard set contains its result; the object emitter does not
select a different operator implementation from an inferred carrier.

Consequently:

- `z / 2` remains `z / 2`; the premises `z $in Z` and `2 != 0` support the
  conclusion that it belongs to `Q`.
- `n - 1` remains `n - 1`; proving it belongs to `N` still requires the
  Litex lower-bound evidence. It must not acquire Lean `Nat.sub` semantics.
- `%`, powers, rounding, real order, and complex operations keep one canonical
  object term. Their domain-specific meaning belongs to the `LitexSet`
  operation laws and proof evidence.

A backend may introduce a native Mathlib value as a local proof witness—for
example, an integer witness obtained from `z $in litexZ`—to reuse a theorem.
Such a **proof view** is local evidence only. It must neither replace the
canonical `z` in the theorem statement nor change the rendering of `z / 2`.

### IR boundary

The implemented context-free object IR has the following shape:

```text
ObjToLeanIR =
    Symbol { symbol_id, name }
  | Number { normalized_value }
  | BuiltinApp { operator, ordered_args }
  | StandardSet { identity }
  | Collection { constructor, ordered_items }

ProofViewToLeanIR = optional native witness and its membership/equality proof
```

Supported Lean emission consumes `ObjToLeanIR` for every displayed object.
The current fact IR still retains the verified source `Fact` for proof
provenance and diagnostics, but IR construction recursively validates every
contained object and target fact operators are monomorphic over `LitexSet`.
A dedicated structural object-fact IR remains a later cleanup; its absence
must not reopen contextual object typing. `ProofViewToLeanIR` may help a
checked proof backend, but it is not an alternative object representation.

The existing raw `Obj` and `Fact` values may remain attached for diagnostics.
An unsupported object constructor, set representation, or operation law must
make report mode `Incomplete` and strict mode fail. It must not trigger a
fallback that assigns the object to `ℝ` or another native carrier.

### Implementation dependency order

```text
structural ObjToLeanIR
  -> one LitexSet target prelude
  -> standard-set values and membership facts
  -> monomorphic equality and order fact interfaces
  -> LitexSet arithmetic and domain laws
  -> optional native proof views
  -> normalization and builtin-rule lowering over the uniform Obj terms
  -> additional Obj families
```

The selected first representation is one concrete inductive `LitexSet`
carrier. Standard sets and unsupported atoms are carrier values; applications
preserve an operator tag and ordered `LitexSet` arguments. A numeral elaborates
through the carrier's `OfNat` instance, so generated source still spells it as
bare `1`. The current real arithmetic backend stores an `ℝ` payload in the
`realValue` constructor and may expose that payload only through a checked
proof view justified by `x ∈ litexR`. Real order, complex arithmetic, modulo,
powers, and rounding still need individual law and proof-view coverage; none
may change the uniform object ABI above.

The first context-free structural tranche contains symbols, numerals, standard
sets, scalar operator nodes already used by the compiler, and the simple set
constructors `union`, `intersect`, `set_minus`, `set_diff`, `big_union`,
`big_intersect`, `power_set`, and list sets. Constructor identity, source
argument order, and list order are preserved. `SetBuilder` is the nearest
rejected boundary because it owns a binder, local facts, and scope; it must fail
during IR construction until a binder-aware IR exists.

The numeric source tracer is
[`to_lean_numeric_obj_abi.lit`](../../examples/05_compiler_interop/to_lean_numeric_obj_abi.lit).
It fixes the unchanged spelling of `z / 2`, natural and integer closure facts,
mixed `Z`/`Q` membership, and the guarded natural-predecessor boundary. The
implemented structural set-object tracer is
[`to_lean_set_obj_abi.lit`](../../examples/05_compiler_interop/to_lean_set_obj_abi.lit);
it covers `union`, `intersect`, and `set_minus`, plus the binder-aware
`SetBuilder` rejection boundary.
