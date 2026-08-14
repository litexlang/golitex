# Litex-to-Lean mathematical design

This document records the target mathematical model for the replacement
Litex-to-Lean compiler. It is normative for new compiler work; the former
native-carrier model is not a compatibility target.

## Universal object universe

Every source-level value, set, standard number domain, function-space object,
and function value is represented by one Lean type:

```lean
namespace Litex

axiom Object : Type

end Litex
```

This type represents Litex object identity. It is not a wrapper around a
hidden per-object Lean carrier, and it has no parameter such as
`Litex.Object α`.

Representative source:

```litex
forall x C:
    x = x
```

Representative target interface:

```lean
∀ (x : Litex.Object) (hxC : Litex.In x Litex.C), x = x
```

The nearest rejected design is a native binder such as `x : ℂ`. That design
would make later membership in an unrelated user set a target typing problem,
although Litex treats it as one more proposition about the same object.

Dependencies: none beyond Lean's `Type`.

Downstream uses: binders, equality, membership, set objects, function objects,
numeric embeddings, and every emitted fact.

Current hole: many source object constructors still lack universal-object
lowering. Unsupported constructors fail closed.

The ABI is packaged once in `lean/Litex/Core.lean`; generated files obtain it
through `import Litex.Rules` alone and do not emit an `abiVersion`
declaration or proof. The nearest rejected packaging repeats the shared
declaration block in every generated file, allowing theorem bodies and semantic
primitives to drift independently.

## Membership and sethood

Membership is an independent proposition:

```lean
namespace Litex

axiom In : Object → Object → Prop
def IsSet (_ : Object) : Prop := True

end Litex
```

A source declaration `x S` binds both `x : Litex.Object` and an exact proof
`Litex.In x S`. It does not make `S` a Lean type. If the runtime later
proves `Litex.In x T`, both membership facts remain available and refer to
the same `x`. Every `Litex.Object` is a set in this model, including values,
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
def Litex.IsNonemptySet (s : Litex.Object) : Prop :=
  ∃ x : Litex.Object, Litex.In x s

def Litex.IsFiniteSet (s : Litex.Object) : Prop :=
  Set.Finite {x : Litex.Object | Litex.In x s}
```

The Mathlib set-builder is only the extension of one universal object under
`Litex.In`; it does not add unrestricted source comprehension. The explicit
always-true `IsSet` predicate records Litex's all-objects-are-sets foundation;
it is not an independent classifier. ABI version 9 implements this definition
directly and removes the redundant sethood conjuncts from the two derived
predicates.

## Standard numeric sets and numerals

`N`, `Z`, `Q`, `R`, `C`, and their supported refinements are
`Litex.Object` constants. A numeral is one `Litex.Object`, not five unrelated
native values. The semantic core embeds Mathlib complex values and
characterizes standard-set membership with witnesses.

```lean
axiom Litex.embedComplex : ℂ → Litex.Object
axiom Litex.R : Litex.Object
axiom Litex.inR_iff {x : Litex.Object} :
  Litex.In x Litex.R ↔ ∃ r : ℝ, Litex.embedComplex (r : ℂ) = x
```

The concrete fact `1 $in R` is proved by
`Litex.Rules.numeralInR`; it is not a generated axiom and is not
accepted merely because the target expected `ℝ`.

The nearest rejected design is `Set.univ : Set ℝ` plus a native
`x : ℝ` binder.

Dependencies: the universal object universe and the numeric embedding
boundary.

Downstream uses: closed numeral membership and arithmetic/order theorems.

Current implementation includes proof-free `Litex.add/sub/mul/div`, numeric
embedding bridges, complex/real closure theorems, adjacent
`N → Z → Q → R → C` projection theorems, and rational normalization. Every
`add/sub/mul` source certificate retains two ordered verifier-owned
`In operand C` proofs; `div` additionally retains the exact
denominator-nonzero proof. Generated theorems replay these facts locally rather
than putting them in object terms. Current holes
include power semantics, transcendental operations, refined numeric-set laws,
and most arithmetic builtin certificates.

## Function-set objects

One source function layer is a restricted specification:

```lean
structure Litex.FnSpec where
  arity : Nat
  requirements : List Litex.Object → Prop
  range : (args : List Litex.Object) →
    args.length = arity → requirements args → Litex.Object

axiom Litex.FnSet : Litex.FnSpec → Litex.Object
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

Named function values and proof-independent anonymous functions are emitted.
The remaining hole is theorem-local replay for compound anonymous bodies and
other dependent owned-binder constructions.

## Proof-free application and exact checked layers

Application denotation is proof-free; applicability is a separate proposition:

```lean
axiom Litex.Applicable : Litex.Object → List Litex.Object → Prop
axiom Litex.apply :
  (f : Litex.Object) → (args : List Litex.Object) → Litex.Object
```

Generated source uses direct list syntax:

```text
f(1, 2, 3) -> f [1, 2, 3]
g(1)(2)    -> (g [1]) [2]
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
- `WellDefinedObjId` for object-proof DAG nodes;
- `WellDefinedFactId` for factual WD obligations;
- phase-labelled root object uses for preflight/proof/store disambiguation;
- child edges, exact target-requirement roles, and source scope.

The emitter names replayable WD facts as
`wd_<environment-depth>_<WellDefinedFactId>`. The depth follows the lexical
forall environment (`0` at the outer level, `1` in its nested forall, and so
on). If an application occurs in a theorem type, the helper theorem is emitted
before the target theorem and generalized over the visible environment.

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

Forall introduction binds every value as `Litex.Object`, then its parameter
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

## Statement definitions and definition replay

An `abstract_prop P(x)` introduces an uninterpreted target predicate
`P : Litex.Object → Prop`. A bodyful concrete proposition is different: its
parameter requirements and clauses determine one target definition. For
example,

```litex
prop is_zero(x R):
    x = 0
```

has the target meaning

```lean
def is_zero (x : Litex.Object) : Prop :=
  Litex.In x Litex.R ∧ x = 0
```

The parameter carrier remains a proposition in the definition body; it never
changes the Lean type of `x`. `by def $is_zero(a)` must carry the exact checked
proofs of `a $in R` and `a = 0`. The emitter validates their order and shapes,
then constructs the conjunction. Conversely, an inferred parameter or clause
fact is projected from the exact source proposition `FactId`; the emitter does
not search for a proposition that happens to match.

An explicit-value object definition such as `have a R = 0` becomes one
`noncomputable def a : Litex.Object := 0`. Its stored type and defining
equality remain separate theorems with stable `FactId`s. The type theorem uses
the verifier-retained check that the value belongs to `R`; the equality is
definitionally proved by `rfl`.

Only an explicit ordinary `trust fact` crosses the source trust boundary and
becomes an axiom. Definition inference, a later repetition of that trusted
fact, and all other stored consequences are theorem declarations or exact
reuses. A repeated `FactId` is accepted only when it denotes the identical
source proposition.

The nearest rejected forms are bodyless concrete `prop`, `trust have`, and
function-valued `have fn`. Their intended target ownership and witness
semantics are not inferred from the supported object-definition case, so they
fail closed.

Dependencies: stable definition lookup, parameter and clause verification
results, `FactId` identity, and the universal-object target.

Downstream uses: reusable named predicates, named explicit values, and checked
definition folding without target proof search.

## Builtin rules

`Litex.Core` contains the small semantic boundary. Each concrete verifier
builtin is represented once by a real Lean theorem in the shared
`Litex.Rules` module. Generated files import that module. The checked
certificate validates its stable rule identity, target, ordered children, and
substitution shape before emitting a call to the theorem.

The first ordinary rule is inequality symmetry:

```lean
theorem Litex.Rules.notEqualSymmetry
    {a b : Litex.Object} (h : a ≠ b) : b ≠ a := by
  exact Ne.symm h
```

The nearest rejected design declares every concrete builtin rule as an axiom.
Only semantic primitives may cross the axiom boundary. Another rejected design
expands the theorem's tactic proof at every use site; Litex has applied one
logical rule, so Lean should check one theorem application there.

Dependencies: structured builtin certificates and the small semantic core.

Downstream uses: replay of verifier automation without target proof search.

Complex and real addition, subtraction, multiplication, and division closure
now use structured certificates and real Lean theorems over proof-free target
terms. Division closure consumes the same two complex-membership facts and
denominator-nonzero fact retained for the source quotient, but those facts are
local proof evidence rather than quotient arguments. Current holes
include power closure and most remaining builtin families.

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
identity, nested forall, basic universal arithmetic, and the first
statement-definition tranche. The next implementation order is:

1. inferred forall;
2. remaining arithmetic operations and numeric hierarchy theorems;
3. user sets and set operators;
4. remaining definitions, anonymous functions, existentials, and proof scopes;
5. transactional report mode and broader real-Mathlib gates.
