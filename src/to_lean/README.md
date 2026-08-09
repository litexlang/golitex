# To-Lean IR MVP

To-Lean no longer re-reads a verified source statement and guesses a tactic
from its syntax. The verifier produces a backend-facing proof IR; the Lean
emitter accepts only that IR.

## Execution contract

`Runtime` has an explicit `to_lean_mode` flag.

- Every fact admitted by runtime storage to an environment's known-fact cache
  receives a runtime-unique `FactId`, in ordinary execution as well as compiler
  execution. Display, nested-binder, and alpha-normalized cache aliases for one
  stored fact share the same ID.
- Ordinary execution leaves `StmtResult::to_lean_ir()` as `None`.
- To-Lean mode attaches `Some(StmtToLeanIR)` only after successful statement
  execution. Fact IR is assembled after storage, so its citations can carry
  stable IDs rather than matching later by display text.
- Local proof premises are distinguished from trusted facts. When a local
  premise was stored in a temporary environment, its ID survives in the
  returned proof IR. The emitter maps it to a proof-space coordinate such as
  `proof_fact_2_3`; that coordinate is not the temporary Litex `FactId`.

The environment cache deliberately stores only `FactId` plus the existing
source location. Proof trees, origins, inferred consequences, local/global Lean
names, and recursive dependencies live in statement results and To-Lean IR.

### Complete and incomplete return values

`to_lean_with_report` is the partial-compilation entrypoint. It returns a
`ToLeanCompilationReport` whose `status` is either `Complete` or `Incomplete`,
whose `lean_code` is always the checked subset that the backend could emit, and
whose `unsupported` list identifies every omitted statement by source index,
rendered statement, path, line, compiler phase, and reason.

Parsing errors, runtime errors, and unverified Litex statements still return
`Err`: those inputs never established a verified source program. Once a
statement has verified, lack of compiler IR or lack of a checked Lean backend
becomes an `Incomplete` diagnostic instead. Report mode continues through later
statements so independent supported declarations are not lost.

Lean emission is transactional per source statement. The emitter checkpoints
its declarations, global `FactId` set, and local-name allocator before lowering
one statement. If any nested proof or inferred fact is unsupported, that whole
statement is rolled back and replaced by a Lean line comment containing the
same diagnostic. It never leaves half of a multi-fact statement behind and
never substitutes `axiom` or `sorry`. The generated source starts with a
machine-readable reader cue such as `-- To-Lean status: incomplete`.

The existing `to_lean`, `to_lean_from_source`, and `emit_lean_from_ir` entrypoints
remain strict and fail closed. Their report counterparts are
`to_lean_with_report`, `to_lean_from_source_with_report`, and
`emit_lean_from_ir_with_report`.

## Environment and proof-scope correspondence

A proof-relevant temporary Litex environment is a semantic scope boundary, not
merely a verifier implementation detail. Whenever verification opens a child
environment and the selected successful route depends on facts introduced or
derived there, the returned `StmtResult` must preserve those facts and their
derivations inside one recursively nested proof unit. It must not leak their
temporary `FactId`s into the parent scope or flatten the result into a global
citation that forgets how the local work was performed.

Within the supported slice, To-Lean lowers that proof unit into a corresponding
nested Lean proof scope, normally a `by` block containing local `intro`, `let`,
`have`, or a theorem-like local lemma. The scope inherits exactly the parent
evidence that was visible to the Litex child environment; facts created inside
it remain local. If a supported local verification step itself opens another
environment and packages several steps before producing a usable fact, its IR
contains another nested proof unit and Lean emits another nested proof scope.
Thus environment nesting determines proof encapsulation and dependency
visibility, even though Litex environments and Lean syntax are not represented
by identical data types.

`ForallIntroduction` is the current concrete example: parameters and premises
installed in its temporary environment survive in the returned proof IR, then
become Lean binders and local `proof_fact` names. A nested known-forall
application similarly becomes a local `have ... := by ...` with its own
`proof_arg` and requirement proofs. The MVP does not yet serialize every
runtime environment as a general-purpose IR node. Purely operational search
environments whose branches were not selected need not be serialized; the
invariant applies to every environment boundary on the successful proof route.
If such a proof-relevant route has no supported nested representation,
compilation must stop instead of flattening away the scope.

## Statement and proof IR

The MVP constructs four statement forms:

- `AbstractProp`
- `Prop`
- `Trust`
- `Fact`

A fact contains its proposition, optional stored `FactId`, and a recursive
`FactProofToLeanIR`. Direct citations are proof-tree leaves. Derived facts use
one general `RuleApplication { rule, parameter_requirements, premises }` node,
so a new transport method extends `ProofRuleToLeanIR` without changing the
recursive proof-tree shape. The first rule vocabulary contains equality and
iff rewrite, definition reduction, normalization, known-forall instantiation,
modus ponens, conjunction/existential introduction, case split, and an explicit
unsupported rule. Only equality rewrite, definition reduction, the supported
normalization slice, known-forall instantiation, and the structured quotient-
nonzero and 20 arithmetic/order builtin rules currently have Lean backends.

### Structured builtin-rule return path

The source-derived coverage ledger is
[`builtin_rule_inventory.md`](builtin_rule_inventory.md). Its generator follows
label arguments through forwarding helpers rather than counting only raw
constructors: 460 direct success-constructor calls currently expand to 656
label-bearing rule/strategy sites, including 560 distinct static labels. Each
row records its Rust source, family, checked Lean mapping, and delivery status;
evaluation/computation-like sites are explicitly outside the current 20-rule
tranche. Twenty-three source sites currently have a checked mapping: the prior
three plus the 20 typed arithmetic/order sites.

A diagnostic rule label is not a proof certificate. A compiler-supported
builtin therefore freezes its successful matcher bindings in
`BuiltinRuleEvidence` before the verifier stack unwinds. The enclosing
`VerifiedByBuiltinRuleResult` keeps that evidence beside the exact recursively
checked `StmtResult` subgoals. If the successful result is later merged into a
`VerifiedBys` sequence, both the evidence and subgoals move together.

Runtime lowering converts the semantic evidence to `BuiltinRuleToLeanIR` and
recursively converts every subgoal to `FactToLeanIR`. The result uses the same
general node as other derived proofs:

```text
RuleApplication {
    rule: Builtin(<typed rule application>),
    parameter_requirements: [...],
    premises: [<recursive child proof IR>, ...],
}
```

Lean emission works back up that tree. It first materializes each child proof
inside the current proof scope, validates that the target and premise
propositions agree with the frozen bindings, and only then applies the Lean
lemma for the parent rule. Thus neither the runtime-to-IR layer nor the emitter
repeats Litex proof search.

This serialization does not widen verifier automation. The existing
`UseBuiltinRuleVerifyState` one-rule recursion budget still controls which
proof tree Litex may select; the compiler only preserves and checks that
already-selected tree.

The first vertical slice is quotient nonzero. For literal-zero targets, the
verifier records the numerator, denominator, and whether the quotient occurred
on the left or right of `!=`. The two subgoals retain the proofs of numerator
and denominator nonzeroness. Lean emits `div_ne_zero hNumerator hDenominator`,
using `Ne.symm` for the reversed target. A resolved identifier that merely
denotes zero still verifies in Litex, but it has no compiler evidence for that
resolution yet; it deliberately remains `OtherUnsupported` rather than
silently treating the identifier as literal zero.

Equality-class lookup retains more than the final equivalent object: it now
returns an ordered path of original equality facts with an orientation for each
edge. A successful atomic-fact transport becomes an `EqualityRewrite` rule;
premise zero proves the source proposition and each following premise proves
the corresponding equality edge. The emitter first reconstructs those known
proofs, then normalizes the cited proposition and target through the recorded
equalities. A citation that changes its proposition without such structured
evidence becomes `OtherUnsupported` rather than an unchecked `exact`.

The equality store remains a compact proof forest rather than an all-pairs
closure or a shortest-path table. Redundant equalities, side branches, and
disconnected classes therefore do not become dependencies merely because they
were visible during verification. While the successful verifier scope is still
alive, it freezes the chosen oriented edges together with the source and edge
`FactId`s into `EqualityTransportEvidence`. To-Lean lowering consumes that
certificate directly; it does not search expired environments or identify an
edge again from printed text. An equality obtained only through a verifier
backend whose derivation is not represented in compiler IR is rejected at this
boundary instead of being emitted without proof provenance.

Known-forall evidence retains each parameter name, structural argument object,
parameter constraint, and recursively verified requirement. Every generated
argument has the one type `LitexSet`. A constraint such as `z Z` is replayed as
the separate proposition `z ∈ litexZ`; it never changes the binder or the
argument into a native integer, rational, or real. The runtime also
instantiates the cited forall's selected conclusion with the recorded objects.
Consequently, `KnownForallInstantiation` proves that direct instance rather
than silently claiming the final goal. If the verifier matched objects that
are rationally equal but print differently, a separate outer `Normalization`
node records the move from the direct instance to the requested goal.
Statement memoization is a transparent proof wrapper and does not erase the
underlying route.

For forall introduction, temporary parameter facts are likewise retained with
their IDs. A `set` parameter needs no extra proposition because every object is
a `LitexSet`; numeric and other domain constraints become named local proofs.
Cached citations and known-forall requirements capture their source `FactId`
while the source environment is alive, so a temporary premise can remain a
local Lean proof argument after its Litex scope has been popped.

## Lean surface

For a standalone file such as `chapter01-introduction.lit`, the generated Lean
surface begins with:

```lean
import Mathlib

namespace chapter01_introduction

noncomputable section

inductive LitexStandardSet where
  | natural | rational | integer | real | complex

inductive LitexSet where
  | realValue (value : ℝ)
  | standard (kind : LitexStandardSet)
  | primitive (tag : String)
  | application (operator : String) (arguments : List LitexSet)

abbrev LitexFact := Prop

-- generated declarations

end chapter01_introduction
```

`LitexSet` is the one meta-level carrier of Litex set-values; it is not itself
a Litex universal-set object. Symbols, numerals, standard sets, arithmetic
applications, and set constructors all elaborate to this carrier. The
`realValue` payload is an internal proof view used by the current Mathlib
arithmetic backend. It does not cause generated statements to print `(z : ℝ)`
or `(1 : ℝ)`.

The emitter never uses a fixed synthetic namespace such as `LitexGenerated`.
A registered file or module uses its canonical Litex name, with `::` mapped to
Lean's `.`, so `A::chap2` becomes `A.chap2`. A standalone runtime whose source
path ends in `.lit` falls back to the sanitized file stem. The canonical name
takes precedence over that fallback.

`to_lean_from_source` remains anonymous and emits declarations at the file
root, even when its diagnostic label looks like a `.lit` path. The pure
`emit_lean_from_ir` boundary is likewise anonymous because IR intentionally
contains no source context. Callers compiling an actual file should use
`to_lean` with that file's Runtime context.

This namespace selection scopes one emitted source. It does not add repository
traversal, Lean imports, or cross-file `FactId` lowering to the current MVP.

The current lowering is intentionally small:

- `abstract_prop` becomes a monomorphic `opaque` proposition over zero or more
  `LitexSet` arguments;
- a typed `prop` over the currently supported parameter surface becomes `def`
  (or `opaque` when it has no body), with object parameters uniformly typed as
  `LitexSet` and nontrivial parameter constraints kept as propositions;
- only an explicit Litex `trust` becomes Lean `axiom`;
- stored proved facts become `theorem global_fact_<FactId>`;
- known-forall application first materializes every chosen object as a
  `LitexSet` `proof_arg_<SpaceId>_<LocalIndex>`, replays every domain requirement
  as a `proof_fact`, and names the direct instantiated conclusion before using
  it;
- definition evidence uses the named Lean definition;
- each generated proof block lazily receives a `SpaceId`; introduced premises
  and intermediate facts are named `proof_fact_<SpaceId>_<LocalIndex>`;
- `proof_arg` and `proof_fact` share one local index stream, so their coordinates
  preserve the actual derivation order inside a proof space;
- a nested proof block inherits visible outer facts; when it first introduces
  a named fact, it receives a fresh `SpaceId` and starts its `LocalIndex` at
  one;
- when a direct forall instance needs checked rational normalization to become
  the final goal, that application is emitted in a nested proof space and the
  outer proof names both the direct instance and normalized result;
- equality transport replays its source, equality edges, and result as
  consecutive `proof_fact` values, with the result checked by
  `simpa only [...] using ...`;
- quotient-nonzero builtin evidence replays its two recursively checked
  nonzero premises and applies `div_ne_zero`, with the recorded target
  orientation deciding whether `Ne.symm` is required;
- arithmetic/order builtin evidence checks the target and ordered premise fact
  families, recursively materializes those premise proofs, and applies one of
  `linarith only`, `mul_nonneg`, `mul_pos`, `div_nonneg`, or `div_pos`;
- verified rational-expression normalization obtains native real witnesses
  only from recorded `x ∈ litexR` proofs, then discharges the proof view with
  `norm_num`, `ring`, or `field_simp` followed by `ring`;
- context-free object lowering preserves symbols, bare normalized numerals,
  standard sets, scalar applications, and the simple set constructors
  `union`, `intersect`, `set_minus`, `set_diff`, `big_union`, `big_intersect`,
  `power_set`, and list sets;
- binder-owning `SetBuilder` remains an explicit IR-construction boundary.

Unsupported proof rules, propositions, objects, parameter types, composite
proofs, and inference origins stop strict compilation with an error. Report
mode instead marks the result `Incomplete`, rolls back and comments the omitted
statement, and continues. Neither mode falls back to `axiom` or `sorry`.

The MVP also requires every cited global `FactId` to have been emitted earlier
in the same IR stream. Facts preloaded during ordinary execution still have
stable IDs, but compiling them through an external Lean library mapping is a
future backend feature; an unresolved preloaded ID is rejected instead of
becoming an undefined Lean name.

## Active tracer

[`examples/05_compiler_interop/to_lean_ir_mvp.lit`](../../examples/05_compiler_interop/to_lean_ir_mvp.lit)
covers the full first vertical slice: abstract proposition, concrete
proposition, trusted forall, explicit known-forall arguments and requirements,
direct-instance-to-goal normalization, definition proof, temporary-premise
reuse, equality transport, forall introduction, and rational builtin proof.

[`examples/05_compiler_interop/to_lean_builtin_rule_ir.lit`](../../examples/05_compiler_interop/to_lean_builtin_rule_ir.lit)
is the builtin-rule tracer. It follows one quotient-nonzero proof from matched
Litex arguments, through recursively returned subgoal results and typed proof
IR, to a checked `div_ne_zero` Lean term. Focused Rust regressions also cover
the reversed target, malformed IR, and the unresolved-zero-alias boundary.

[`examples/05_compiler_interop/to_lean_builtin_rules_20.lit`](../../examples/05_compiler_interop/to_lean_builtin_rules_20.lit)
is the representative 20-rule tracer. It covers strict-to-weak order,
subtraction signs, addition signs and monotonicity, multiplication signs, and
division signs. A focused regression requires 20 distinct typed rule IDs,
rejects malformed premise arity, and sends the complete generated module
through the real Lean kernel.

[`examples/05_compiler_interop/to_lean_partial_report.lit`](../../examples/05_compiler_interop/to_lean_partial_report.lit)
is the completeness tracer. Its supported rational equalities surround one
verified but unsupported trigonometric rule. Report mode returns
`Incomplete`, identifies statement 2, emits statements 1 and 3, and produces
Lean accepted by the real kernel; strict mode still rejects the same unsupported
rule.

[`examples/05_compiler_interop/to_lean_numeric_obj_abi.lit`](../../examples/05_compiler_interop/to_lean_numeric_obj_abi.lit)
is the numeric-object semantic tracer. It fixes source-side membership facts,
uniform object spellings, and the guarded natural-subtraction boundary.

[`examples/05_compiler_interop/to_lean_set_obj_abi.lit`](../../examples/05_compiler_interop/to_lean_set_obj_abi.lit)
is the implemented structural object tracer. It sends `union`, `intersect`,
and `set_minus` through `ObjToLeanIR` and the one-carrier prelude, while a
focused negative regression requires `SetBuilder` to fail during IR
construction.

Rust and Litex gates:

```text
cargo test --release to_lean:: -- --nocapture
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/to_lean_ir_mvp.lit
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/to_lean_builtin_rules_20.lit
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/to_lean_set_obj_abi.lit
```

Actual Lean-kernel gate (requires an already-fetched Mathlib Lake project):

```text
LITEX_LEAN_PROJECT=/path/to/mathlib-project \
LITEX_LAKE=/optional/absolute/path/to/lake \
  cargo test --release generated_to_lean_mvp_compiles_with_lean -- --ignored --nocapture
LITEX_LEAN_PROJECT=/path/to/mathlib-project \
LITEX_LAKE=/optional/absolute/path/to/lake \
  cargo test --release generated_to_lean_builtin_rules_20_compiles_with_lean -- --ignored --nocapture
LITEX_LEAN=/absolute/path/to/lean \
  cargo test --release generated_to_lean_set_obj_abi_compiles_with_lean_core -- --ignored --nocapture
```

For scratch work, these commands first verify `examples/tmp.lit`,
`examples/tmp1.lit`, or `examples/tmp2.lit`, generate the corresponding Lean
translation, and append it to that file inside a triple-quoted Litex comment.
`tmp2.lit` is also the equality-path gallery, including clean, reversed,
redundant, branched, disconnected, repeated-argument, and independent paths.

```text
cargo test --release run_tmp0_to_lean -- --nocapture
cargo test --release run_tmp1_to_lean -- --nocapture
cargo test --release run_tmp2_to_lean -- --nocapture
```

The source file is left unchanged when verification or Lean generation fails.
Before writing a successful snapshot, the command removes the last
triple-quoted block when that block is at the end of the file. Triple-quoted
blocks elsewhere in the source are preserved.

Implementation lives in `src/to_lean_ir`,
`src/runtime/runtime_to_lean_ir.rs`, and `src/to_lean`.
