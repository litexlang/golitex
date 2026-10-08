# Litex to Lean object and interoperability design

The current design preserves Litex's membership-based mathematical world while
using typed Lean representations and explicit evidence. Every usable object
contains its WD proof. Litex-owned constructions remain the primary interface;
proved adapters expose ordinary Lean/Mathlib values and theorem statements.

The initial Core and numeric interoperability example compile. Automatic
object lowering and verifier-proof replay are still future work. The example
targets are handwritten expected output, not compiler-generated artifacts.

## Settled object contracts

The object interface is mandatory, not an optional wrapper:

```lean
-- Abbreviated shape; actual source is universe-polymorphic.
structure Obj {M : Semantics} (α : Type) [Representation M α] where
  val : α
  wd : WD (M := M) val
```

α is a host representation type, not a source mathematical classification.
An object a keeps that type when new `In a R` or `In a C` facts become available.
Representation fixes its admissibility and meaning for the compiled context;
there is no fallback certifying every arbitrary Lean type.

Numeric leaves keep native payloads, currently `Litex.number (1 : ℂ)`.
Other constructions use Litex-owned representations. Standard R/C are objects,
not host types ℝ/ℂ. AddObj/DivObj contain certified children and return certified
objects:

```lean
Litex.add a b haC hbC
Litex.div a b haC hbC hb0

-- Starting from raw representatives and their WD evidence:
Litex.add ⟨a, wa⟩ ⟨b, wb⟩ haC hbC
```

Child WD is inside the operands. The additional facts justify this operation:
two C-memberships for addition, and semantic nonzero for division. They enter
the result's root WD. Proof arguments do not add mathematical arguments or
change the represented value. The returned object already contains its WD;
its membership remains a distinct fact needed by later constructions.

WD reflects source formation and admissibility. It is not the fact that a Lean
term has some host type, and sethood alone does not justify an otherwise
undefined division. Every certified object has sethood evidence through its
fixed representation contract.

## Facts and target statements

Under one fixed Semantics model, Core defines:

```lean
Same a b := denote a = denote b
In a A   := M.mem (denote a) (denote A)
IsSet a  := M.isSet (denote a)
```

Same is heterogeneous mathematical equality. It compares fixed meanings and
supports substitution; it does not generally identify raw host payloads.
Membership is an ordinary proposition and observes both arguments. Denotation
reads values only, independently of WD or membership proof choice.

Common source facts become theorem conclusions:

| Source | Target shape |
| --- | --- |
| `1 = 1` | `Same (number 1) (number 1)` |
| `$is_set(1)` | `IsSet (number 1)` |
| `1 $in R` | `In (number 1) R` |
| `forall a C: a = a` | generic certified a and `In a C` imply `Same a a` |
| `forall a R: a $in C` | `In a R` implies `In a C` without changing a or α |
| `forall a C: a + 0 = a` | `Same (add a (number 0) haC (numberInC 0)) a` |
| guarded division | `div a b haC hbC hb0`, preserving the nonzero obligation |

These rows abbreviate source formatting and shared Lean context. Exact,
checked declarations are in [Statements.lit](InteropExamples/Statements.lit)
and [ExpectedTarget.lean](InteropExamples/ExpectedTarget.lean).

A source declaration such as `have a C` supplies an object and its membership
fact to subsequent statements. In a theorem interface, that context is a
generic `a : Obj α` plus `haC : In a C`. Closed-module witness selection and
statement execution have not been compiled yet; this context description does
not turn the declaration into a new Lean axiom.

## Core and proof ownership

Core owns representations, construction/WD contracts and reusable mathematical
laws. The future compiler must consume the current verifier's successful
evidence and translate it into applications of those laws. It must preserve
scope, operand identities, guards and referenced facts. Equality-class and
builtin-rule evidence belong to the new pipeline, not the archived one.

The first lowerer should traverse the existing Obj AST using a prepared,
immutable context of represented objects and named Lean proofs. Its initial
scope is exact integer leaves, R/C, bound identifiers and owned add/div. Missing
bindings or required evidence are explicit compilation failures. No source
AST evidence fields, fabricated proof names, target-side proof search or new
axioms are needed for that interface.

After object lowering, add statement-context formation and evidence replay for
reflexivity, sethood, standard membership/inclusion and the supported numeric
rules. Tuples/finite sets and then functions/guards/application are later
object slices. Function internals remain Litex-owned; native arrows are an
adapter interface. These extensions are plans, not implemented coverage.

Later functions must preserve fixed signature domains/return sets, ordered
guards, exact argument arity and application layers, and coherent internal
member/result presentations. Body formation/WD and return membership are
separate obligations; an empty admitted domain does not waive body formation.
The return set is an upper bound, not a label that changes function graph identity.

## Native Lean consumption

Keep the responsibilities explicit:

| Layer | Responsibility |
| --- | --- |
| Source .lit | Mathematical statements and Litex proofs |
| Target .lean importing Core | Typed object construction and eventually exact verifier-proof replay |
| Adapter | Native input conversion, live target-proof citation and proved output conversion |
| Final | Ordinary Lean/Mathlib theorem statements and use through Adapter |

An adapter packages native complex inputs with `number`, or real inputs with
`number (r : ℂ)` and real-membership evidence. It invokes the target theorem
and consumes the returned proof. It converts Same to native equality only
through a faithful numeric interpretation, using number injectivity and the
add/div correspondence laws. Generic C-members also have a unique native
complex view with denotation and proof-independence laws; taking that view does
not replace the source object or its host type.

The final statement must contain only ordinary Lean/Mathlib binders,
hypotheses and conclusions:

```lean
theorem complexAddZero (x : ℂ) : x + 0 = x := by
  exact Adapter.complexAddZero x

theorem realAddZero (x : ℝ) : x + 0 = x := by
  exact Adapter.realAddZero x
```

Its proof may call Adapter. Model, WD and bridge assumptions must not leak into
that statement. The adapter converts the interface rather than proving the
mathematical result again. See [Adapter.lean](InteropExamples/Adapter.lean),
[Final.lean](InteropExamples/Final.lean) and
[NativeBridge.lean](Litex/NativeBridge.lean).

## Concrete model and verified scope

Conditional Core theorems alone cannot close a native theorem without an actual
model. The interoperability adapter explicitly chooses the proved
[NumericModel.model](InteropExamples/NumericModel.lean) inside its proof.

This example uses genuine Mathlib ZFSet values/membership, an injective numeric
encoding and actual N/Z/Q/R/C range sets. It satisfies the current numeric
Semantics contract. Its chosen well-order encoding is an example, not a
production decision. Numeric-code membership depends on that encoding, and
the full source foundation/object families have not been interpreted. The
model's outside-C decode fallback does not authorize operations without WD.

On October 8, 2026, seven source statements passed the strict Litex gate. All
14 Lean files passed warnings-as-errors checks; four negative boundaries were
rejected; 19 audited declarations used only the standard Lean/Mathlib axioms.
The compiled adapter has a live target-proof dependency, and Final also passes
normal `lake env lean`. These checks establish the example interfaces and
native reuse; they do not establish automatic compiler correctness or complete
Litex model adequacy.

Commands, exact evidence and scope are in the
[interoperability README](InteropExamples/README.md) and
[source journal](InteropExamples/proof_journals/statements.json).
Legacy material remains local and ignored under `scripts/legacy_to_lean/`;
its execution pipeline is not the basis for new proof compilation.
