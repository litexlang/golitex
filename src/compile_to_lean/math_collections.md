# Litex-to-Lean mathematical design

This document records the target mathematical model for the replacement
Litex-to-Lean compiler. It is normative for new compiler work; the former
native-carrier model is not a compatibility target.

## Universal object universe

Every source-level value, set, standard number domain, function-space object,
and function value is represented by one Lean type:

```lean
axiom LitexObject : Type
```

This type represents Litex object identity. It is not a wrapper around a
hidden per-object Lean carrier, and it has no parameter such as
`LitexObject α`.

Representative source:

```litex
forall x C:
    x = x
```

Representative target interface:

```lean
∀ (x : LitexObject) (hxC : Litex.In x Litex.C), x = x
```

The nearest rejected design is a native binder such as `x : ℂ`. That design
would make later membership in an unrelated user set a target typing problem,
although Litex treats it as one more proposition about the same object.

Dependencies: none beyond Lean's `Type`.

Downstream uses: binders, equality, membership, set objects, function objects,
numeric embeddings, and every emitted fact.

Current hole: many source object constructors still lack universal-object
lowering. Unsupported constructors fail closed.

## Membership and sethood

Membership is an independent proposition:

```lean
axiom Litex.In : LitexObject → LitexObject → Prop
def Litex.IsSet (_ : LitexObject) : Prop := True
```

A source declaration `x S` binds both `x : LitexObject` and an exact proof
`Litex.In x S`. It does not make `S` a Lean type. If the runtime later
proves `Litex.In x T`, both membership facts remain available and refer to
the same `x`. Every `LitexObject` is a set in this model, including values,
standard numeric domains, and function objects. A source `x set` fact may
still be retained by `FactId`; being definitionally trivial in Lean is not a
reason to erase verifier evidence.

This is the central application rule:

```litex
forall a C, f fn(x R) R:
    a = 1
    =>:
        a $in R
        f(a) = f(a)
```

The application passes `a` together with the retained proof of
`Litex.In a Litex.R`. It performs no cast from `C` to `R`.

The nearest rejected source omits the proof of `a $in R`; Litex must reject
`f(a)` as not well-defined before target emission.

Dependencies: the universal object universe and runtime-owned membership
facts.

Downstream uses: bounded forall parameters, function-domain checks, user-set
facts, and standard-set facts.

Current hole: general set constructors and set builtin theorems have not yet
been ported to this ABI.

Nonemptiness and finiteness are derived rather than added to the semantic
axiom boundary:

```lean
def Litex.IsNonemptySet (s : LitexObject) : Prop :=
  ∃ x : LitexObject, Litex.In x s

def Litex.IsFiniteSet (s : LitexObject) : Prop :=
  Set.Finite {x : LitexObject | Litex.In x s}
```

The Mathlib set-builder is only the extension of one universal object under
`Litex.In`; it does not add unrestricted source comprehension. The explicit
always-true `IsSet` predicate records Litex's all-objects-are-sets foundation;
it is not an independent classifier. The current emitted prelude has not yet
migrated from opaque `IsSet` and redundant derived-predicate conjuncts; that
implementation drift is recorded in `current_generated_file_header.lean`.

## Standard numeric sets and numerals

`N`, `Z`, `Q`, `R`, `C`, and their supported refinements are
`LitexObject` constants. A numeral is one `LitexObject`, not five unrelated
native values. The semantic core embeds Mathlib complex values and
characterizes standard-set membership with witnesses.

```lean
axiom Litex.embedComplex : ℂ → LitexObject
axiom Litex.R : LitexObject
axiom Litex.inR_iff {x : LitexObject} :
  Litex.In x Litex.R ↔ ∃ r : ℝ, Litex.embedComplex (r : ℂ) = x
```

The concrete fact `1 $in R` is proved by
`Litex.BuiltinRules.numeralInR`; it is not a generated axiom and is not
accepted merely because the target expected `ℝ`.

The nearest rejected design is `Set.univ : Set ℝ` plus a native
`x : ℝ` binder.

Dependencies: the universal object universe and the numeric embedding
boundary.

Downstream uses: closed numeral membership and arithmetic/order theorems.

Current implementation includes unified `Litex.add/sub/mul/div`, their numeric
embedding bridges, real-closure theorems, and rational normalization. Current
holes include power semantics, transcendental operations, refined numeric-set
laws, and most arithmetic builtin certificates.

## Function-set objects

One source function layer is a restricted specification:

```lean
structure Litex.FnSpec where
  arity : Nat
  requirements : List LitexObject → Prop
  range : List LitexObject → LitexObject

axiom Litex.FnSet : Litex.FnSpec → LitexObject
```

Each parameter-set membership and each declared domain condition contributes
one ordered conjunct to `requirements`. The range is a set object and may
itself be a function-set object.

The nearest rejected design is a native dependent function type. Native
currying would blur source application boundaries and would bind membership
conditions into Lean types.

Dependencies: universal objects, membership, and exact source function-type
IR.

Downstream uses: parameter facts, application well-definedness, and
function-valued returns.

Current hole: anonymous function values and named function definitions are not
yet emitted.

## Proof-carrying application and exact layers

Application consumes an explicit proof:

```lean
axiom Litex.Applicable : LitexObject → List LitexObject → Prop
axiom Litex.apply :
  (f : LitexObject) → (args : List LitexObject) →
  Litex.Applicable f args → LitexObject
```

Generated source uses direct list syntax:

```text
f(1, 2, 3) -> f [1, 2, 3] proof
g(1)(2)    -> (g [1] firstProof) [2] secondProof
```

`Litex.fnSetResult` proves that the result of one layer belongs to its
declared range. When that range is another `FnSet`, this exact membership is
used to justify the next layer.

The nearest rejected source is `f(1)(2, 3)` for
`f $in fn(x, y, z R) R`. Litex rejects the first layer's arity; target
currying must not repair it.

Dependencies: function-set membership, ordered requirement proofs, and
application-layer IR.

Downstream uses: every named function call.

Repeated structurally equal applications have distinct parser-owned source
occurrence IDs. A cache hit maps the later occurrence to the same retained WD
proof and fact IDs; changing or omitting that occurrence link fails closed.

## Well-definedness evidence

Litex verifies object well-definedness before the enclosing fact. The
parser/runtime retain:

- `SourceObjectOccurrenceId` for every parsed application occurrence;
- `WellDefinedObjProofId` for object-proof DAG nodes;
- `WellDefinedFactId` for factual WD obligations;
- child edges, exact target-requirement roles, and source scope.

The emitter names replayable WD facts as `well_defined_fact_<id>`. If an
application occurs in a theorem type, the helper theorem is emitted before the
target theorem and generalized over the visible environment.

A cache hit creates another exact source-occurrence use of the earlier proof.
It does not become a proofless boolean and the emitter does not rediscover the
fact by proposition text. Parent, discarded-child, and committed-child proof
visibility follows the Litex environment chain.

Statement execution labels preflight, proof, and store WD uses. When the proof
phase rechecks an application, its edge is the canonical target edge because
its cited `FactId`s belong to the final proof scope; otherwise the preflight
edge remains canonical. Every proof node remains in the audit DAG, and Lean
helpers are still emitted before the theorem type that consumes them.

The nearest rejected state is a target application for which no accessible,
proposition-matching retained WD fact exists.

Dependencies: verifier-owned IDs, scope visibility, and fact proof IR.

Downstream uses: `Litex.fnSetApplicable` and auditability of source-only WD
checks.

Current hole: broader source constructors still need to expose target-use
roles through the same identity chain.

## Fact replay and forall

Every stored source fact has a stable `FactId`. A direct citation resolves
only that ID. A known-forall use retains:

1. the source theorem `FactId`;
2. explicit object arguments;
3. ordered parameter requirements;
4. ordered domain proofs;
5. the selected conclusion.

Forall introduction binds every value as `LitexObject`, then its parameter
fact, then domain facts. It never derives a Lean binder type from a set.

Known equality has one mathematical representation plus an identity join.
`KnownEquality` keeps both the union-find classes used by ordinary verification
and the direct proof forest behind those classes. The existing fact cache maps
each selected direct equality to its stable `FactId`. When a goal such as
`b = a` or `a = c` succeeds by class membership, the verifier reads one
connected `KnownEquality::proof_path`, joins every edge to its cached identity,
and freezes that path before the local scope closes. Lean then replays it with
`Eq.symm` and `Eq.trans`.

The nearest rejected representation stores the transitive closure without its
direct sources, or lets the emitter rediscover an equality by proposition
text. Either representation loses which local proof is in scope.

The nearest rejected implementation uses `assumption`, proposition-string
matching, or target proof search.

Dependencies: `KnownEquality` direct proof paths, stable runtime `FactId`
values, environment scope/merge semantics, and projected-forall proof IR.

Downstream uses: modular theorem replay and WD facts proved from earlier
theorems.

Current hole: supported inferred-forall premises are not yet emitted.

## Builtin rules

The prelude contains a small semantic core. Each concrete verifier builtin is
then represented by a real Lean theorem under `Litex.BuiltinRules`. The
checked certificate validates its target and ordered children before emitting
a call to that theorem.

The first ordinary rule is inequality symmetry:

```lean
theorem Litex.BuiltinRules.notEqualSymmetry
    {a b : LitexObject} (h : a ≠ b) : b ≠ a := by
  exact Ne.symm h
```

The nearest rejected design declares every concrete builtin rule as an axiom.
Only semantic primitives may cross the axiom boundary.

Dependencies: structured builtin certificates and the small semantic core.

Downstream uses: replay of verifier automation without target proof search.

Real addition, subtraction, multiplication, and division closure now also use
structured certificates and real Lean theorems. Current holes include power
closure and most remaining builtin families.

## Trust and incomplete output

Only explicit source `trust` may emit an axiom for the trusted proposition.
The compiler may not invent membership, WD, function contracts, builtin laws,
or unsupported statement axioms.

Strict mode fails closed. Transactional report mode remains unfinished: it
must roll back one unsupported source statement and report it without
`sorry` or an implicit axiom.

## Implementation order

The current executable slice covers the universal ABI, primary membership/WD
tracer, exact FactId replay including known-equality paths, known forall,
ordinary builtin theorems, exact named-application layers, source occurrence
identity, nested forall, and basic universal arithmetic. The next
implementation order is:

1. inferred forall;
2. remaining arithmetic operations and numeric hierarchy theorems;
3. user sets and set operators;
4. definitions, anonymous functions, existentials, and proof scopes;
5. transactional report mode and broader real-Mathlib gates.
