# Litex-to-Lean compiler

The compiler replays verifier-produced proof IR over one universal Lean object
type. It does not translate Litex set membership into Lean typing.

## Ownership boundary

`Runtime` executes Litex. Compiler entry points temporarily set
`Runtime::well_defined_capture` to a capture session so the verifier preserves
the evidence that exists only while local environments are alive. Ordinary
execution leaves that field as `None`.

`LitexToLeanCompiler` owns all construction of `LitexToLeanStatementIr` and
borrows `Runtime` read-only. `Runtime` invokes it at the successful statement
completion boundary, before a surrounding proof environment can disappear,
and stores the resulting IR snapshot in the `StmtResult`. Lean emission then
consumes only compiler IR.

The public `capture_litex_to_lean_ir_from_source` entry point exposes that same
verified IR to the independent compiler2 module under
`src/litex_to_lean_compiler2`.
It does not change the existing universal-object emitter or the `-lean` CLI.
Direct closed equality reported by the verifier as `calculation` is retained as
a zero-premise rational-normalization certificate only after the IR builder
rechecks the exact equality with the verifier's calculation predicate.

The consolidated target design and its ten representative examples are in
[`litex_object_design.md`](litex_object_design.md). The shared ABI is owned by
[`Litex.Core`](../../lean/Litex/Core.lean), concrete builtin theorems by
[`Litex.Rules`](../../lean/Litex/Rules.lean), and the exact import
plus ABI check emitted today is checked in as
[`current_generated_file_header.lean`](current_generated_file_header.lean).
The design ledger explicitly marks decisions that the current emitter has not
implemented yet.

## Target ABI

Every Litex value, set, standard numeric set, function-space object, and
function value has target type `Litex.Object`:

```lean
namespace Litex

axiom Object : Type
axiom In : Object → Object → Prop
def IsSet (_ : Object) : Prop := True

def IsNonemptySet (s : Object) : Prop :=
  ∃ x : Object, In x s

def IsFiniteSet (s : Object) : Prop :=
  Set.Finite {x : Object | In x s}

end Litex
```

For example, source `a C` contributes both an object binder and a membership
proof:

```lean
(a : Litex.Object)
(haC : Litex.In a Litex.C)
```

If Litex later proves `a $in R`, the target retains a second proposition
`Litex.In a Litex.R`. The object is not converted from `ℂ` to `ℝ`; neither of
those native types is its Lean type.

Generated top-level `forall` types stay on one line while they remain short.
When the rendered type exceeds 100 characters, the emitter puts each adjacent
binder pair on a continuation line and the conclusion on a separate line.
This formatting does not shorten `Litex.*` names or change declaration types.

Every `Litex.Object` is a set in the decided target model. `IsNonemptySet` and
`IsFiniteSet` are not separate axioms; they classify the object's membership
extension. The `Set.Finite` expression is only a Mathlib view of that
extension; source sets remain `Litex.Object` values. The shared `Litex.Core`
implements this boundary definitionally, while generated source still retains
the exact source sethood binders and `FactId`s.

The builtin `$is_choice_function_for(I,S,g,f)` is likewise emitted as the
defined proposition `Litex.IsChoiceFunctionFor I S g f`, quantified over
members of `I` and the exact applicability proofs for `f` and `g`. It is not an
uninterpreted target axiom. The `S` argument remains in the public arity while
its carrier obligations are supplied by Litex well-definedness.

The removed backend used native binders, `Set.univ : Set ℝ`, carrier joining,
widening, and downcast rejection. Those files and the carrier IR were deleted.
They are not a compatibility backend.

## Function objects

Ordinary `fn(...) ...` types use the readable `Litex.fnSpace` interface. The
compiler emits `fnSpace1` through `fnSpace5` for one to five parameters and
`fnSpace [A, B, ...] R` for larger arities:

```text
fn(x R) R                 -> Litex.fnSpace1 Litex.R Litex.R
fn(x R, y C) R            -> Litex.fnSpace2 Litex.R Litex.C Litex.R
fn(a A, b B, ..., f F) R  -> Litex.fnSpace [A, B, ..., F] R
```

`Litex.FnSpec` remains the advanced representation for dependent parameter
sets, dependent result sets, and extra domain conditions. It is intentionally
absent from ordinary generated function-space types.

The source application layers are preserved exactly:

```text
f(a, b) -> f [a, b]
f(a)(b) -> (f [a]) [b]
```

`Litex.Applicable f args` is constructed separately from the exact retained
function-set membership, argument memberships, and domain facts. Lean currying
never makes an invalid Litex application valid. `FnSpec.requirements` packages
those facts as an ordered dependent existential telescope in `Prop`; both
`FnSpec.range` and `functionObject`'s body may use the same arity and
requirements evidence, while `apply` and `functionObject` denotations do not
take the selected WD proofs as object arguments.

Named `have fn` definitions render a proof-free body. Their `closed` theorem
introduces the function telescope and then replays the verifier-owned body WD
DAG locally: `x + 1` cites the retained complex-membership facts, and `1 / x`
cites the exact domain `FactId` for `x != 0`. Later definition reduction unfolds
only the cited defining equality and uses the exact locally named application
certificate.
Anonymous functions use the same ABI. Compound bodies replay their WD and
return-membership DAG under the anonymous function's own binder telescope;
the `functionObject` term itself remains proof-free.

## Proof evidence

`LitexToLeanStatementIr` mirrors `Stmt` recursively: top-level variants such
as `DefObjStmt` retain their source child enum, and payload IR types keep the
corresponding source statement names. Backend normalization lives inside those
payloads and shared emitter functions; it does not rename statements into
effect-shaped public variants.

The parser and runtime assign stable `SourceObjectOccurrenceId`, `FactId`,
`WellDefinedFactId`, and `WellDefinedObjId` values while the successful
Litex scopes still exist. Every source application, checked arithmetic node,
and checked list set has an occurrence ID. The backend consumes
those IDs; it does not match rendered propositions or rerun proof search.

- A known fact cites its exact `FactId`.
- A known equality-class proof freezes an ordered path of direct equality
  `FactId`s. The emitter validates every edge and replays only `Eq.symm` and
  `Eq.trans`; it never searches the equivalence class again.
- A known forall cites its theorem `FactId`, explicit object arguments,
  parameter membership/set-property proofs, and domain proofs.
- Compiler-owned Lean identifiers use the reserved `__` prefix. Source Litex
  names beginning with `__` are rejected, while ordinary source names
  (including names beginning with one underscore) remain available. Typical
  generated names are `__fact43`, `__h0_1`, `__wd0_7`, `__obj44_app`, and
  `__obj44_result`.
- Advanced function specifications use `__arg_0`, `__arg_1`, ... for nested
  argument-list binders. A named function implementation uses `__fn_arg`,
  `__fn_arg_len`, and `__fn_arg_req` for its argument list and evidence.
- A WD fact is named from its exact `WellDefinedFactId` and replayed as a local
  `have` after the binders of its owning theorem or function-closure proof.
- Selected WD objects and transitive children are traversed in dependency
  order. Their denotations remain proof-free; applications additionally get
  local `__objN_app` and `__objN_result` proof bindings. Arithmetic
  objects retain `C` as an intrinsic result carrier and likewise get a local
  `__objN_result` when no already-named `WellDefinedFactId` proves that exact
  membership. Rolled-back verifier search nodes are not part of the statement
  certificate and emit nothing.
- Equal source applications retain different occurrence IDs. If the second
  occurrence hits Litex's WD cache, both occurrence-use edges cite the same
  object proof and factual proof. Its unvisited nested occurrences are mapped
  to cached child IDs by the verifier-owned positional child recipe. The
  runtime labels preflight, proof, and store rechecks explicitly and freezes
  one exact occurrence-to-object edge; the emitter never selects a candidate
  by semantic key, execution phase, or whether Lean happens to prove it.
- Closed arithmetic manufactured by a verifier proof is not a source
  occurrence. The supported numeral-only case is replayed by the shared
  numeral and arithmetic-closure theorem schema with every WD premise
  explicit; it does not manufacture a fake occurrence ID.
- A builtin certificate calls a real theorem imported from the shared
  `Litex.Rules` module. Concrete builtin rules are not axioms.
- Only explicit source `trust` may emit an axiom for the trusted proposition.

The shared `Litex.Core` module declares the universal object universe,
membership, numeric embedding/coherence, restricted function application, and
primitive object constructors. This boundary interprets Litex. Ordinary
verifier rules are proved once in `Litex.Rules` from that core and
Mathlib; generated files import the module and never repeat those proof bodies.

## Current strict slice

The replacement emitter currently covers the architecture tracer and its
supporting routes:

- abstract proposition declarations and explicit trusted facts;
- bodyful concrete proposition definitions, including parameter constraints;
- explicit-value object definitions with checked membership and defining
  equality facts;
- `by def` proposition folding and definition-clause projection through exact
  retained child proofs and `FactId`s;
- atomic equality, inequality, membership, and basic set predicates;
- standard sets and natural numerals;
- forall introduction and exact projected-forall `FactId`s;
- direct known facts and known-forall instantiation;
- `by cases` and atomic `by contra` with recursively emitted local proof
  statements, branch-local WD certificates and `FactId`s, exact conjunction
  introduction/projection, and nested cases/contradiction scopes;
- non-exporting `example` goals as Lean `example : P := by ...`, and targetless
  `sketch` blocks as `example : True := by ...`, with all retained statements
  replayed as local proof facts;
- equality transport and object reflexivity;
- direct known-equality symmetry and transitivity through exact `FactId`
  paths;
- closed numeral membership through proved builtin theorems;
- ordinary not-equality symmetry through a proved builtin theorem;
- named function spaces and exact one-layer or nested proof-free applications
  with local WD helpers and `Litex.fnSetResult` between layers;
- named function definitions with proof-free `+`, `-`, `*`, `/` bodies, local
  ordered parameter/domain evidence, exact return membership, and checked
  definition reduction;
- nested forall replay with retained temporary parameter `FactId`s;
- `Litex.add/sub/mul/div`, real arithmetic closure theorems, and rational
  normalization for the arithmetic tracer.
- big union/intersection, power set, general Cartesian products, half-open and
  closed integer ranges, tuple/sequence literals, finite/infinite sequence
  carriers, and indexed or finite-set `sum`/`product`/`reduce` object terms;
- compound anonymous-function bodies under their exact binder-owned WD scope,
  including integer addition used as a reduction operation.

Unsupported statements or proof rules fail closed. They are not translated by
the deleted backend and do not become `sorry` or implicit axioms.
In particular, the current strict slice does not yet replay the
`by axiom_of_choice` or `by zorn_lemma` statement certificates. The
`general_cart` and big-set object denotations now lower, but non-reflexive
choice, membership, and algebraic proofs still require their own checked
`Litex.Rules` adapters.
Bodyless concrete `prop`, `trust have`, and function-valued `have fn` also
remain explicit errors; they are not treated as definitions or target axioms.

## Inspecting the complete ledger output

The primary executable ledger is one Litex file containing commented,
independent `sketch` blocks. Refresh its checked-in Lean counterpart with:

```text
target/release/litex -lean \
  lean/examples/compile_to_lean_examples.lit \
  lean/examples/compile_to_lean_examples.lean
```

Each sketch is emitted in an isolated namespace, so declarations, named
theorems, and explicit trusted axioms do not collide across examples. The CLI
also supports freshly compiling every `litex` fence under a level-two heading
in the detailed Markdown ledger and collecting the results in one Lean file:

```text
target/release/litex -lean-ledger \
  lean/examples/compile_to_lean_examples.md \
  private/compile-to-lean-generated.lean
```

The equivalent Cargo test entrypoint is deliberately ignored by the ordinary
test suite because it leaves the inspection file in `private/`:

```text
cargo test --release dump_compile_to_lean_ledger -- --ignored --nocapture
```

The output hoists shared imports once and places each ledger entry in its own
numbered namespace, so the combined file can be inspected or compiled without
declaration-name collisions. Markdown Lean snapshots and required-shape blocks
are ignored: every output section comes from a fresh Litex compilation. The
output path is replaced only after every Litex entry compiles successfully.

## Evidence

The primary acceptance source is
[`compile_to_lean_litex_object_abi.lit`](../../lean/examples/cases/compile_to_lean_litex_object_abi.lit).
The shared-builtin-library tracer is
[`compile_to_lean_shared_builtin_rules.lit`](../../lean/examples/cases/compile_to_lean_shared_builtin_rules.lit).
The nested-forall/arithmetic/occurrence tracer is
[`compile_to_lean_arithmetic_forall_wd.lit`](../../lean/examples/cases/compile_to_lean_arithmetic_forall_wd.lit).
The named well-defined-object DAG tracer is
[`compile_to_lean_well_defined_object_dag.lit`](../../lean/examples/cases/compile_to_lean_well_defined_object_dag.lit).
The derived-set-predicate tracer is
[`compile_to_lean_set_predicate_definitions.lit`](../../lean/examples/cases/compile_to_lean_set_predicate_definitions.lit).
The known-equality path tracer is
[`compile_to_lean_known_equality_path.lit`](../../lean/examples/cases/compile_to_lean_known_equality_path.lit).
The first statement-definition tracer is
[`compile_to_lean_first_statement_tranche.lit`](../../lean/examples/cases/compile_to_lean_first_statement_tranche.lit).
The anonymous proof-block tracer is
[`compile_to_lean_example_and_sketch.lit`](../../lean/examples/cases/compile_to_lean_example_and_sketch.lit).
The append-only executable feature history is in
[`compile_to_lean_examples.md`](../../lean/examples/compile_to_lean_examples.md).

Focused Rust tests live beside `universal_pipeline.rs`. Ignored real-kernel
tests use `LITEX_LEAN_PROJECT` and optional `LITEX_LAKE` to compile
`Litex.Core`, `Litex.Rules`, and the complete generated source with
Mathlib.
