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
