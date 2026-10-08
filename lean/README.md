# Initial Litex Lean object interface

This directory implements the initial object construction interface and a
checked numeric interoperability example. A Litex-to-Lean compiler, proof
replay engine and complete source mathematical model remain unimplemented.

The accepted object, compilation and native-consumer contracts are recorded
in [DESIGN.md](DESIGN.md), including the current verified scope and next work.

Every object has a host payload and its own WD proof:

```lean
structure Obj {M : Semantics} (α : Type) [Representation M α] where
  val : α
  wd : WD (M := M) val
```

The actual source is universe-polymorphic. The semantic parameter M is fixed
for a compiled unit. Representation fixes a carrier's meaning and admissibility;
there is no default instance for arbitrary Lean types. These parameters are
visible obligations, not global project axioms. The example-only
`InteropExamples/NumericModel.lean` supplies a concrete instance of the current
numeric contract; it does not establish correctness of a complete Litex model
or select the production numeric encoding.

## Files

- `Litex/Semantics.lean`: standard-set tags and the explicit model contract.
- `Litex/Objects.lean`: Representation, WD, mandatory Obj, heterogeneous Same,
  membership, sethood, native complex leaves and standard-set objects.
- `Litex/Arithmetic.lean`: owned AddObj/DivObj payloads and constructors.
- `Litex/NumericRules.lean`: a proved addition-by-zero rule from the model contract.
- `Litex/NativeBridge.lean`: domain-restricted, faithful native numeric conversions.
- `Litex.lean`: public import.
- `examples/ObjectMvp.lean`: number, R/C, generic object, addition, division
  and nested division constructions under supplied facts.
- `InteropExamples/`: paired source/expected targets, numeric model, adapter
  and native consumer; see [its README](InteropExamples/README.md).
- `tests/`: interface/interop checks and four intentionally rejected inputs.
- `check.py`: reproducible focused checks with local output files.

Core N/Z/Q have standard-set leaves; their full exported membership hierarchy
is future work. The example model interprets all five as actual numeric range
sets. R/C have explicit semantic membership and inclusion contracts.
Numeric leaves currently use native ℂ payloads. Decimal lowering, other native
numeric carriers, tuples, finite sets and functions follow later.

## Object construction

Under the fixed M and registered host representations:

```lean
Litex.number (M := M) (1 : ℂ)
Litex.add a b haC hbC
Litex.div a b haC hbC hb0
```

Operands already carry WD. Addition's root WD stores the two C-memberships;
division additionally stores semantic nonzero. Returned objects contain that
WD. Domain proofs do not enter the payload or select the mathematical meaning.
Same compares fixed mathematical denotations, not the raw host values or WD
proofs. Membership observes both represented arguments.

An identifier stays Obj α after obtaining R/C membership. An arithmetic
expression returns Obj (AddObj α β) or Obj (DivObj α β), rather than native
arithmetic replacing the owned representation. Native numeric correspondence
is part of the explicit Semantics contract and is instantiated in the example
model for a checked native consumer.

## Check

The package pins Lean and Mathlib v4.31.0. In an initialized Lake project, run:

```sh
cd lean
lake build Litex
python3 check.py
```

For an existing pinned Mathlib cache, check without rebuilding or modifying it:

```sh
python3 lean/check.py --packages-dir /path/to/cached/lake/packages
```

The script checks the pinned Mathlib revision, compiles to local
`lean/.lake/build/lib/lean`, verifies objects and the native consumer, requires
four negative inputs to fail, and audits 19 public declarations for project
axioms and proof holes. It also verifies the compiled adapter consumes its
expected target theorem and does not import archived Litex outputs. The negative fixtures
are intentionally invalid and must not be treated as ordinary build targets.

Core laws remain model/representation parameters. The closed native example
discharges its model parameters with NumericModel; it adds no hidden model
hypotheses to the native theorem. No automated theorem replay, source proof
search or full-system mathematical soundness is established by this gate.

The initial check on October 8, 2026 passed with Lean 4.31.0: all six source
modules/examples/checks compiled with warnings as errors, all three negative
fixtures were rejected, and the eight audited declarations used only
`propext`, `Classical.choice` and `Quot.sound`. A separate stdin `import Litex`
check resolved the new Obj/add/div interfaces from local outputs.

The subsequent interoperability gate passed all 14 Lean files, four negative
fixtures, 19 axiom audits and the compiled adapter's live target-proof dependency.
The native Final file also passed through normal `lake env lean`.
All seven paired source statements passed the separate strict Litex gate.

## Legacy archive

The former `lean/` project and `litex_semantics_in_lean/` draft were moved intact
to the local ignored workspace `scripts/legacy_to_lean/`. Old generated proofs,
receipts and tools are historical material; their original paths/commands are
not current build instructions. The archive is not part of the public tree.
