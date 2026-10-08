# Litex-to-Lean Compiler Guide

This guide explains the design principles of Litex-to-Lean compilation through
concrete source/generated examples. It is the maintained entry point for why
the compiler works this way and what its output means.

The [compiler README](../src/compile_to_lean/README.md) describes implementation
details, internal design rationale, result types, and extension points. Keep
reader-facing explanations and example walkthroughs here; keep Rust control
flow and replay bookkeeping there. [CLI documentation](cli.md#lean-compiler-boundary)
owns the command-line contract.

## From a checked fact to a Lean proof

The smallest example is [one equals itself](../lean/examples/one_equals_itself/statement.lit):

```litex
1 = 1
```

Its [generated Lean file](../lean/examples/one_equals_itself/statement.lean)
contains this declaration, shown verbatim without the surrounding namespace:

```lean
theorem fact_1 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))
```

`Litex.number` represents the source number; `Litex.Same` expresses source
equality through the objects' meanings. The proof uses `Litex.sameRefl` because
the successful Litex result records identical endpoints. This gives the
compiler its central job: replay the proof route Litex actually checked.

Run the standalone source and inspect compiler output separately:

```sh
target/release/litex -strict -lang en -f lean/examples/one_equals_itself/statement.lit
target/release/litex -strict -lean -f lean/examples/one_equals_itself/statement.lit
```

The second command writes Lean source to stdout. Generating that source and
checking it with the Lean kernel are separate steps.

## Compile the evidence behind the fact

A successful source run contains more than its final propositions. It records
the selected verification route, object well-definedness evidence, child
proofs, and citations to earlier facts. Compilation consumes those typed
results in source order.

For `1 = 1`, the recorded route is reflexivity. For a fact such as
`a + 0 = a`, a selected rational-normalization route must go through its
normalization adapter. Recognizing the final equality and substituting an
unrelated add-zero theorem would lose the connection to the source proof.
Fixed normalization within the selected adapter may discharge a numeric
certificate; it does not authorize unrestricted target proof search.

This distinction also sets the support boundary: a proposition can be
verifiable in Litex while its particular evidence route is outside the current
compiler. Such a route needs an explicit adapter before compilation can accept
it.

## Definitions and named theorem citations

The [named add-zero example](../lean/examples/named_add_zero/statement.lit)
combines a proved interface, a typed value and an expression alias:

```litex
thm add_zero:
    ? forall x R:
        x + 0 = x

have offset R = 2
let shifted = offset + 0
by thm add_zero(offset) => offset + 0 = offset
shifted = offset
```

Its [generated file](../lean/examples/named_add_zero/statement.lean) defines the
certified alias objects and emits a named theorem. The explicit call applies
that earlier theorem and its source argument-membership proof, then selects the
actual returned equality. The last line follows the recorded equality path
through the alias and the proved result. Compilation does not replace the call
with a fresh arithmetic proof.

The source theorem's goal WD and proof body have separate captured scopes.
Replaying both preserves their actual parameter and premise producers; local
proof definitions do not become later global declarations. Repeated forall
facts use their recorded earlier theorem and binder renaming when that is the
source's selected route.

The [equality transport example](../lean/examples/equality_membership_transport/statement.lit)
shows another use of citations:

```litex
forall u,v C:
    u = v
    u $in R
    =>:
        v $in R
```

The proof consumes the given equality and real-membership fact. It transports
membership through denotation equality while retaining both objects' generic
host representations.

## Membership preserves the object's representation

The [generic complex-object example](../lean/examples/complex_object_equals_itself/statement.lit)
extends reflexivity to a parameter:

```litex
forall a C:
    a = a
```

In its [generated file](../lean/examples/complex_object_equals_itself/statement.lean),
the parameter remains an object with a generic host representation. These are
verbatim fragments of the generated theorem header, separated for readability:

```lean
{_Host_i1 : Type v1}
[_rep_i1 : Litex.Representation M _Host_i1]
(_value_i1 : Litex.Obj (M := M) _Host_i1)
(_h_param_i1 : Litex.In _value_i1 (Litex.C (M := M)))
```

`a C` supplies a membership fact. It does not replace the object's representation
with a Lean `ℂ` variable. The theorem's conclusion is
`Litex.Same _value_i1 _value_i1`, proved by `Litex.sameRefl _value_i1`.

The semantic interface in [lean/Litex.lean](../lean/Litex.lean) packages each
object's value with its well-definedness proof:

```lean
structure Obj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  val : α
  wd : WD (M := M) val
```

The representation fixes the value's meaning independently of the chosen WD
proof. Numeric literals can use native complex payloads; generic parameters
and constructed expressions retain their own representations. Proved bridges
connect their meanings to native numeric mathematics when the required
membership evidence is available.

## Construction conditions survive compilation

The [division example](../lean/examples/division_equals_itself/statement.lit)
shows why proving an equality starts with certifying its objects:

```litex
forall a C, b C:
    b != 0
    =>:
        a / b = a / b
```

Even this reflexive equality requires a well-defined quotient. The
[generated file](../lean/examples/division_equals_itself/statement.lean) introduces
complex-membership proofs for both parameters and the nonzero premise for `b`.
The quotient passed to reflexivity is this verbatim generated expression:

```lean
Litex.div _value_i1 _value_i2 _h_param_i1 _h_param_i2 _h_dom_f1
```

The three proof arguments certify the two operand domains and the nonzero
denominator. They preserve source conditions; they are not additional
mathematical operands. Compilation must establish or resolve this exact
construction evidence before emitting the equality proof.

## Citations and assumptions retain their scopes

In the division example, `b != 0` belongs to the universal theorem's local
context. It cannot become a premise for an unrelated later theorem. The same
restriction applies to local objects, cached WD evidence, and cited facts.

Replay identifies citations by their recorded IDs and checks their subjects.
A cached construction must resolve to the already replayed evidence for that
object. If an ID is missing, or a required inferred fact has no supported
producer, compilation rejects the route. Searching for another true fact in
the live environment would hide the missing source dependency.

## What successful output establishes

Generated declarations currently expose an explicit semantic parameter:

```lean
variable {M : Litex.Semantics.{u}}
```

The Lean theorem is conditional on that interface. `lean/Litex.lean` includes
an explicit candidate numeric model, but it does not yet provide a completed
interpretation of all Litex objects and rules. Native Lean/Mathlib consumers
also require proved representation bridges and, where needed, a handwritten
adapter. That adapter is a separate artifact from compiler-generated output.

Acceptance has three distinct parts:

1. **Source verification:** the exact Litex source succeeds, and its selected
   evidence is identified.
2. **Compilation:** the compiler consumes that evidence and generates a
   complete artifact. An unsupported statement, constructor, proof route,
   citation, or scope rejects the whole artifact.
3. **Generated-file and Lean checks:** regeneration matches the maintained
   paired file, and the generated proof plus semantic interface pass the
   pinned Lean/Mathlib kernel with the intended assumption boundary.

No proof hole or newly invented axiom may stand in for an unsupported route.
`-strict` excludes source trust and user axioms; it does not establish that
every Litex foundation already has a complete Lean interpretation.

## Maintaining this guide

Keep new design explanations connected to a real source/generated pair under
[lean/examples/](../lean/examples/). Each walkthrough should state the
mathematical fact, the selected source proof route, what the generated proof
preserves, and its nearest unsupported boundary. Label proposed designs and
unverified examples explicitly.

The snippets above are excerpts of the maintained examples and semantic
interface, not an exhaustive capability inventory. Update them when their
owning artifacts change. Keep implementation mappings in the
[compiler README](../src/compile_to_lean/README.md), and keep development
fixtures, receipts, and build tooling in the local-only compiler workspace
`scripts/litex_to_lean/`.
