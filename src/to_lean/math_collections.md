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

The current `LeanRationalExpression` implementation assigns real annotations
to numbers as an MVP implementation detail. It is not the permanent object
ABI.

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

The Lean target needs one representation type for a Litex object and one type
for Litex sets. Their exact implementation remains a backend design choice,
but their interface is fixed at this level:

```text
LitexObj
LitexSet

litexN, litexZ, litexQ, litexR, litexC : LitexSet
membership : LitexObj -> LitexSet -> Prop
```

Thus the semantic shape of the tracer is:

```text
forall z Z:
    z / 2 $in Q

->

forall z LitexObj:
    z $in litexZ
    =>:
        z / 2 $in litexQ
```

The target binder's single `LitexObj` annotation is global compiler
scaffolding; it is not a temporary claim that `z` is a Lean integer, rational,
or real. Every occurrence in the translated object remains the bare symbol
`z`.

Standard-set inclusion is likewise preserved as mathematics about objects:

```text
litexN subset litexZ subset litexQ subset litexR subset litexC
```

Refined sets such as `N+`, `Z*`, and `Q-` remain set values or membership
predicates. They are not Lean subtypes attached to each symbol.

### Numerals obtain constraints from facts, not annotations

A `Number` node lowers to its normalized spelling and nothing else. For
example, the object in `1 $in R` is emitted as `1`, and the containing
membership proposition supplies the `LitexObj` expectation:

```text
1 $in litexR
```

It is not emitted as `(1 : ℝ)`. Likewise, `q + 1` keeps the bare literal `1`.
Closed equality and order facts must use monomorphic Litex fact interfaces, or
another enclosing `LitexObj` expectation, so Lean never needs to default an
otherwise unconstrained numeral to `Nat`. That constraint belongs to fact
lowering, not to `Obj` lowering.

This separation is important because a Litex numeral may have many true
memberships. Prematurely assigning `1` to `Z`, `Q`, or `R` would manufacture
different target terms for one source object and could select the wrong target
operator, such as integer division.

### Operators stay attached to the object universe

Each Litex operator has one target operation on `LitexObj`. The verifier's
well-definedness and membership evidence controls where that operation may be
used and what standard set contains its result; the object emitter does not
select a different operator implementation from an inferred carrier.

Consequently:

- `z / 2` remains `z / 2`; the premises `z $in Z` and `2 != 0` support the
  conclusion that it belongs to `Q`.
- `n - 1` remains `n - 1`; proving it belongs to `N` still requires the
  Litex lower-bound evidence. It must not acquire Lean `Nat.sub` semantics.
- `%`, powers, rounding, real order, and complex operations keep one canonical
  object term. Their domain-specific meaning belongs to the `LitexObj`
  operation laws and proof evidence.

A backend may introduce a native Mathlib value as a local proof witness—for
example, an integer witness obtained from `z $in litexZ`—to reuse a theorem.
Such a **proof view** is local evidence only. It must neither replace the
canonical `z` in the theorem statement nor change the rendering of `z / 2`.

### IR boundary

The first implementation tranche should introduce shapes equivalent to:

```text
ObjToLeanIR =
    Symbol { symbol_id, name }
  | Number { normalized_value }
  | Add | Sub | Mul | Div | Mod | Pow | ...
  | StandardSet { identity }

ObjFactToLeanIR =
    Equality { left: ObjToLeanIR, right: ObjToLeanIR }
  | Order { relation, left: ObjToLeanIR, right: ObjToLeanIR }
  | Membership { element: ObjToLeanIR, set: ObjToLeanIR }

ProofViewToLeanIR = optional native witness and its membership/equality proof
```

Supported Lean emission consumes `ObjToLeanIR` for every displayed object.
`ObjFactToLeanIR` supplies the monomorphic fact context needed by the target
elaborator. `ProofViewToLeanIR` may help a checked proof backend, but it is not
an alternative object representation.

The existing raw `Obj` and `Fact` values may remain attached for diagnostics.
An unsupported object constructor, set representation, or operation law must
make report mode `Incomplete` and strict mode fail. It must not trigger a
fallback that assigns the object to `ℝ` or another native carrier.

### Implementation dependency order

```text
structural ObjToLeanIR
  -> one LitexObj / LitexSet target prelude
  -> standard-set values and membership facts
  -> monomorphic equality and order fact interfaces
  -> LitexObj arithmetic and domain laws
  -> optional native proof views
  -> normalization and builtin-rule lowering over the uniform Obj terms
  -> additional Obj families
```

The concrete representation of `LitexObj`—for example, an abstract model with
laws or a model backed by a sufficiently broad Mathlib domain—must be tested
against real order, complex arithmetic, modulo, powers, and rounding before it
is selected. That backend choice may affect proof construction, but it may not
change the uniform object ABI above.

The persistent source tracer is
[`to_lean_numeric_obj_abi.lit`](../../examples/05_compiler_interop/to_lean_numeric_obj_abi.lit).
It fixes the unchanged spelling of `z / 2`, natural and integer closure facts,
mixed `Z`/`Q` membership, and the guarded natural-predecessor boundary.
