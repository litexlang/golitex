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
theorem h_1 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
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

The Rust entrypoint makes the execution and compilation stages explicit:

```rust
let result = runtime.run_litex_code(&source)?;
let compiler = LitexToLeanCompiler::new(runtime);
let lean = compiler.compile_run(&result, &artifact_namespace)?;
```

The compiler takes ownership of Runtime and receives the completed result as a
method parameter, then dispatches the existing `ExecStmtResult` and its typed
child enums. Runtime is moved without cloning; the compiler has only that one
field and no lifetime parameter. Its files mirror the
executor's statement and verification branches. Each branch reads its original
subject and selected evidence, compiles its children, and produces temporary
Lean expressions. It does not maintain a second object, fact, theorem or
parameter model.

A borrowed source-position cursor identifies the original result ancestors and
completed stage prefix. This preserves earlier citations and local boundaries
without copying ExecEnv or maintaining a separate proof registry. Source IDs
spell every source proof declaration and reference as `h_<original FactId>`,
including parameters, guards, inferred facts and named theorems. Statement
positions determine execution order; they do not allocate proof names.
Parameter signatures come from the declaration's original
position, so a later `have` cannot extend an earlier theorem's inputs.

An object's constructor can depend on a local membership or nonzero proof.
If its exported proposition uses that proof name, the generated type includes
the necessary actual proof expressions as local `let` values. This closes the
Lean expression without turning proved facts into new theorem assumptions.

Runtime executes the source once, then moves into the compiler as a read-only
exact-ID resolver.
The current result is not self-contained after Runtime disposal: some source
stages retain IDs rather than complete producer payloads. `compile_run` returns
source only when the whole artifact succeeds. The method can receive another
result without retaining earlier output. The free `compile_run` delegates to
the same implementation and now also takes Runtime by value.

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

## Finite sets and bounded builders

[The finite natural set](../lean/examples/finite_natural_set/statement.lit)
retains its source elements and the proof that they are distinct:

```litex
have small_naturals set = {1, 2}
1 $in small_naturals
small_naturals $subset N
```

The actual generated representation nests certified `Litex.insert` objects.
Each child keeps its own host representation. Source `{1, 1}` and
`{1 + 1, 2}` remain rejected, although native set insertion permits duplicates.
Enumeration order is construction order; mathematical identity is extensional.

[Nonnegative rational inclusion](../lean/examples/nonnegative_rational_subset/statement.lit)
uses bounded separation:

```litex
have nonnegative_rationals set = {x Q: x >= 0}
have nonnegative_reals set = {x R: x >= 0}
nonnegative_rationals $subset nonnegative_reals
```

`Litex.setBuilder` owns the certified bound and a predicate on certified members.
Its predicate WD is formation evidence, not a claim that the predicate is true.
Ordered filters retain preceding proof witnesses: in
`{x R: x != 0, 1 / x > 0}`, the nonzero proof certifies the division. Empty
bounds require no witness; a selected empty-domain universal result consumes
its recorded emptiness proof before contradiction elimination.

`SetSemantics M` is proved by the actual ZF model. Function domains inherit
its same separation operation. Arbitrary `have A set` and `forall A set`
retain generic host representations; `set` does not denote a universal set.
A native numeric view observes only numeric members. Interpreting the whole
set as a real or complex set additionally needs a proved `A $subset R` or
`A $subset C`. Native consumers close the reviewed model inside their proof
bodies and expose ordinary ZFSet, Set Complex and Set Real statements.

This slice supports atomic and flat And/chain filters and supported concrete
predicates, with the exact recorded membership/subset routes. General compound logic,
nonempty/finite binder kinds, unbounded comprehension and existence-based
set selection are outside this compiler profile. They do not become axioms.

## Formula functions and concrete predicates

The [guarded reciprocal](../lean/examples/guarded_real_reciprocal/statement.lit)
defines a formula with an ordinary nonzero requirement:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

Its generated object uses `Litex.formulaFn`; evaluation uses `Litex.call`.
The call's WD contains the recorded function-space membership, argument
membership and guard proofs. References to stored source proofs use their
original `h_<FactId>` names. A newly checked numeric requirement can instead
contain its selected proof expression directly. Library parameter names such
as `hf` do not rename source citations.

`FunctionSemantics M` adds graph construction and evaluation to the numeric
interface. The concrete instance proves these laws with Mathlib ZF sets;
the source function remains an owned graph object. Its internal value-body
callback does not replace the source object with a native real arrow.

The current slice supports one or two fixed N/Z/Q/R/C inputs and output,
numeric RHS/let carrier aliases, direct and concrete-predicate function guards,
and top-level concrete predicates with atomic or flat And/chain
defining clauses. [Nonnegativity](../lean/examples/nonnegative_real_property/statement.lit)
demonstrates predicate definition and unfolding; [quotient distribution](../lean/examples/real_quotient_distributes/statement.lit)
demonstrates two arguments. The
[composed formula](../lean/examples/composed_real_formula/statement.lit) calls
earlier one/two-input functions in its body, while the
[chain guard](../lean/examples/chain_guard_reciprocal/statement.lit) retains a
concrete predicate's two inequalities before constructing the reciprocal.
Recursive and higher-order formula bodies remain outside this slice.

The [natural successor](../lean/examples/natural_successor_affine_identity/statement.lit)
also preserves the natural return condition:

```litex
have fn f(x N) N = x + 1
forall n N:
    2 * f(n) = 2 + 2 * n
f(2) = 3
```

The signed-membership result retains its original zero WD before storing
nonnegativity; `Litex.addInN` proves the body's natural membership.
[Natural polynomial formulas](../lean/examples/natural_polynomial_formulas/statement.lit)
and [integer polynomial formulas](../lean/examples/integer_polynomial_formulas/statement.lit)
also preserve N multiplication, Z arithmetic and closed nonnegative powers
through the original membership certificates. N subtraction and Z division
still require their actual additional conditions; arithmetic syntax alone
does not establish those closures.
The [shifted square quotient](../lean/examples/real_shift_square_quotient/statement.lit)
replays a selected `ArithmeticCongruence` residual: exact recorded requirement
facts, IDs and successful children produce ordinary congruence of the semantic
operations.

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

The [direct nested call](../lean/examples/nested_named_add_zero/statement.lit)
needs no preliminary object-construction statement. This block includes the
`add_zero` declaration so it can run independently:

```litex
thm add_zero:
    ? forall x R:
        x + 0 = x

thm add_zero_again:
    ? forall y R:
        y + 0 = y
    by thm add_zero(y) => y + 0 = y
```

Its result retains `selected_wd`, checked in the caller after the invocation
scope closes and before storage. Call-local WD cannot replace that evidence.

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

## Rational aliases, arbitrary numeric contexts and real order

The [rational half example](../lean/examples/typed_rational_half/statement.lit)
keeps the literal and owned-division object distinction:

```litex
have half Q = 1 / 2
half + half = 1
```

Its [actual generated file](../lean/examples/typed_rational_half/statement.lean)
replays Q membership and the stored defining equality, substitutes the recorded
closed expression through the two add operands, then consumes the actual closed
residual proof. Q denotes the faithful rational image; membership never changes
the alias's host type. A fixed certificate normalizer checks the recorded scalar
values rather than finding another proof of the final goal.

The [arbitrary real example](../lean/examples/arbitrary_real_laws/statement.lit)
starts with a context declaration:

```litex
have arbitrary_real R
arbitrary_real + 0 = arbitrary_real
arbitrary_real >= arbitrary_real
```

The compiler checks the recorded nonempty proof and emits a generic certified
object and In-R hypothesis. Later theorem headers retain those parameters; it
does not define the object to be zero. Top-level declarations remain context
parameters. Inside a named proof, the
[local witness example](../lean/examples/local_witness_additive_identity/statement.lit)
instead eliminates the recorded nonempty carrier inside that proof:

```litex
thm local_witness_cancel:
    ? forall x R:
        x+0=x
    have y R
    (x+0)+y=x+y
```

The selected cancellation uses the local witness, but the exported statement
still quantifies only over the original `x` and its membership. Numeric and
set-kind local have, dependent typed-have and let have separate evidence and
scope checks. A local prop/function definition or nested named theorem remains
a separate unsupported scope extension.

[Real squares](../lean/examples/real_squares_nonnegative/statement.lit) and
[weak-order transitivity](../lean/examples/weak_order_transitivity/statement.lit)
use ordinary `Litex.Le`/`Litex.Lt` facts, with greater comparisons represented by
reversing their arguments. Their meanings contain real denotation witnesses;
there is no order on arbitrary complex objects. The compiler replays the actual
R-domain conditions before the selected order theorem and retains its source
premises, exact citations and even-exponent restriction.

## Membership preserves the object's representation

### The explicit mathematical interpretation M

Every generated file declares its interpretation explicitly:

```lean
variable {M : Litex.Semantics.{u}}
```

`M` is a proof-bearing mathematical dictionary. `M.Value` is the common
semantic universe; `M.mem` and `M.isSet` interpret membership and sethood.
`M.number : ℂ → M.Value` embeds native numbers, `M.standard` interprets
N/Z/Q/R/C, and the arithmetic fields interpret the owned Litex operations.
The dictionary also contains proofs of the required laws.

`Representation M α` fixes how a host value of type `α` denotes an element
of `M.Value` and which host values are well-defined. `Obj α` carries that
host value together with its WD proof. Source facts concern its denotation:

```text
a.val : α  -- Representation.denote -->  Litex.denote a : M.Value

Litex.In a A   = M.mem (Litex.denote a) (Litex.denote A)
Litex.Same a b = (Litex.denote a = Litex.denote b)
```

The generated theorem holds for every `M` satisfying this interface; the
compiler does not fix a default interpretation. Current native consumers
explicitly instantiate `Litex.NumericModel.model`, whose values are Mathlib
ZF sets. This is a concrete model of the supported slice, not a completed
interpretation of every Litex object and rule. Function-using output also
requires the separate proved `Litex.FunctionSemantics M` contract.

### Membership supplies knowledge without changing α

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
(h_15 : Litex.In _value_i1 (Litex.C (M := M)))
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

### A native numeric representative for a generic object

The [real-is-complex source](../lean/examples/real_is_complex/statement.lit)
checks `forall a R: a $in C`. Its generated theorem keeps the generic
host, `Representation`, certified object and ordinary In-R hypothesis, and
proves In-C with `Litex.realToComplex`. No conversion of the host type occurs.

The `Semantics` contract guarantees a unique native complex representative
of each complex member. These are the relevant existing fields:

```lean
number_injective : Function.Injective number
complex_members : ∀ x, mem x (standard .complex) ↔ ∃ z, x = number z
```

Core exposes `Litex.NativeBridge.asComplex a h_16 : ℂ` and proves that its
embedding equals the object's denotation. An illustrative handwritten
adapter body follows; `h_2` abbreviates the generated real-is-complex theorem,
and `a`, `M`, `α` and `h_15` come from its context:

```lean
have h_16 : Litex.In a Litex.C := h_2 a h_15
let z : ℂ := Litex.NativeBridge.asComplex a h_16
have hz : Litex.denote a = M.number z :=
  Litex.NativeBridge.asComplex_spec a h_16
```

This observation works for any `M : Semantics`, not only NumericModel.
`asComplex_proofIndependent` proves independence from the membership proof;
`same_iff_asComplex` identifies semantic equality with equality of native
complex representatives. `asReal` similarly observes real members, and
`asComplex_eq_asReal` proves compatibility with the native real-to-complex
embedding. The observations use classical choice and are noncomputable.
They leave the original object and its host representation intact. Equality
of observations does not imply equality of arbitrary host payloads, because
`Representation.denote` need not be injective.

The compiler already uses this bridge in the
[add-zero generated proof](../lean/examples/add_zero/statement.lean): the
source sum stays `Litex.add`, while `asComplex`, `asComplex_spec` and
`denoteAdd` supply numeric witnesses to check the source-selected rational
normalization. An observation does not replace the owned operation or select
a new proof route. A handwritten native Adapter consumes generated proofs
through these proved conversions; its Final consumer can expose ordinary
Mathlib binders and propositions.

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
Litex.div _value_i1 _value_i2 h_28 h_29 h_1
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

Additive cancellation replays the stored inference, including its original
membership checks, derived WD and fact identity. For example:

```litex
forall a, b, k R:
    a + k = b + k
    =>:
        a = b
```

The compiler emits the inferred equality under its original `h_<FactId>`
before the conclusion cites it. The [cancellation example](../lean/examples/additive_cancellation/statement.lit)
also covers a shared addend in different positions and nested rational sums.
The four cancellation laws in `Litex.lean` are proved from numeric denotation,
faithful complex embedding and ordinary additive cancellation.

The compiler also replays the source's subtractive, multiplicative and division
cancellation results. For example:

```litex
forall a,b,k R:
    k!=0
    a*k=b*k
    =>:
        a=b
```

Subtraction supports `a-k=b-k` and `k-a=k-b`. Multiplication supports all four
direct common-factor positions. Common-denominator division requires `k!=0`;
`k/a=k/b` requires the numerator and both denominators to be nonzero. Each rule
retains its own evidence and calls a proved Core law. Nested cancellation
replays the actual recursive stores before their later citations. Removing a
producer, guard or WD certificate rejects compilation; none becomes a premise.
The [multiplication example](../lean/examples/multiplicative_cancellation/statement.lit)
includes all positions and a nested rational product.

Definition folding also compiles inside named theorem bodies:

```litex
prop is_nonnegative(x R):
    x>=0
thm squares:
    ? forall x R:
        $is_nonnegative(x^2)
    by def $is_nonnegative(x^2)
```

This consumes the original by-def result, including goal WD, the selected
definition proof and its stores. The caller's completed formation can supply
later WD citations; a constructor checked only inside a closed defining clause
cannot escape. The [generated pair](../lean/examples/nonnegative_square_property_theorem/statement.lean)
also contains an explicit invocation of the named property theorem.

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

## Using a generated result in ordinary Mathlib

The supported mathematical subset has 18 selected roles: numeric hierarchy,
exact rational arithmetic, rational closure, complex algebra, real order,
equality transport, arbitrary numeric values, aliases, concrete predicates,
guarded formula functions, named theorem citations and bounded sets. The
reciprocal-product example combines these roles in an additional integration
case. Companion regression examples do not count as new selected roles.

For the [quotient-distribution source](../lean/examples/real_quotient_distributes/statement.lit),
the chain is source → original typed result → generated theorem → handwritten
Adapter → ordinary native Final. The generated statement retains generic
objects, WD and the denominator's nonzero evidence. The Adapter specializes
the reviewed model and proves the representation conversion. The local Final
exports this ordinary Mathlib theorem:

```lean
theorem realQuotientDistributes (x y z : ℝ) (hz : z ≠ 0) :
    (x + y) / z = x / z + y / z := by
  exact Adapter.realQuotientDistributes x y z hz
```

With that local `native.Final` module available, a Lean client can use it:

```lean
import native.Final

theorem useCompiledQuotient (x y z : ℝ) (hz : z ≠ 0) :
    (x + y) / z = x / z + y / z := by
  exact NativeConsumer.realQuotientDistributes x y z hz
```

The client statement contains only real numbers, arithmetic and the ordinary
nonzero premise. Local Adapter/Final files are handwritten acceptance tooling
under ignored `scripts/litex_to_lean/native/`; they are not an automatically
published Lean package. In another pinned Mathlib project, import the saved
generated module and `Litex.lean`, then provide a reviewed Adapter/Final for
the native interface you need. Keep the relative generated-module import path
and the source file's actual namespace. Membership proofs permit native
observations without changing the original object's host representation.

The local selected-subset check is:

```sh
cargo build --release
python3 scripts/litex_to_lean/check.py --subset --work-area .draft/selected-subset --profile-area .draft/selected-subset/replay-profiles
```

It records source/generated hashes, actual typed-result field paths and
selected rule/certificate tags, real Lean checks, standard-axiom audits and
native proof-reference paths. The helper compiles the same original result
whose Detailed projection it records; JSON is audit presentation, not compiler
input. The matrix has one row per selected mathematical role. Native proof
references are inspected after beta/zeta reduction, including helper paths;
dead local lets and lambda arguments do not count as a generated-proof use.
This checks structural proof dependencies, not mathematical necessity or a
formal proof of the whole Rust translation.

The interpretation of an arbitrary set illustrates a deliberate interface
difference: `$is_set(A)` has a generated proof, while native `A : ZFSet`
already expresses sethood through its type. No artificial native sethood
predicate is needed. Numeric views of a whole set still need subset evidence.
The selected slice leaves modules, general existential witness declarations,
unbounded comprehension, existence-based set choice, recursive/higher-order formula bodies
and unsupported inference/certificate routes outside the compiler boundary.
An observed unused inference node in a result trace does not establish
compiler support for that inference.

## Composing the mathematical slice

The [compound-return example](../lean/examples/named_compound_theorem_returns/statement.lit)
selects individual facts from named chain and conjunction returns:

```litex
thm square_packages:
    ? forall x R:
        x*x=x^2=x*x
        0<=x^2 and x*x=x^2
    x*x=x^2=x*x
    0<=x^2 and x*x=x^2
thm nonnegative_square_from_package:
    ? forall x R:
        0<=x^2
    by thm square_packages(x) => 0<=x^2
```

The compiler consumes the actual invocation's domain proofs and captured
domain stores, then forms every returned conclusion before publishing its
stored components. Selection cites an original direct component FactId. A
later fact uses the caller's own recorded WD; compound constructors inside a
closed invocation are not exported. Numeric literals and standard sets retain
the existing closed-leaf rule. The second wrapper in the complete example
selects the product equality from the chain. The local handwritten native
consumer combines these two generated wrapper proofs into
`(x : ℝ) → 0 ≤ x ^ 2 ∧ x * x = x ^ 2`.

The [predicate-transport example](../lean/examples/concrete_predicate_equality_transport/statement.lit)
uses semantic equality to transfer a concrete property before a guarded call:

```litex
prop transport_nonnegative(x R):
    x >= 0
have fn transport_guarded_square(x R: $transport_nonnegative(x)) R = x^2

forall a,b R:
    a=b
    $transport_nonnegative(a)
    =>:
        $transport_nonnegative(b)
        transport_guarded_square(b)=b^2
```

The declarations in this block define nonnegativity and a square function guarded
by that property. The selected proof cites the previous predicate fact and
the ordered equality evidence. Since the predicate is defined on semantic
denotations, Lean's congruence and equality elimination transfer that cited
proof. This does not require equality of the objects' host payloads, and their
host types stay generic. The native consumer exposes ordinary reals:
`(a b : ℝ) → a = b → 0 ≤ a → 0 ≤ b`.

The [natural polynomial example](../lean/examples/natural_polynomial_formulas/statement.lit)
also defines a concrete property of the natural-output square function.
Natural membership's original nonnegative inference is emitted once, with its
own FactId. Predicate and bounded-builder clauses can reuse literal WD from
completed parameter inference. A pending inference still cannot cite its own
future fact, even if an ancestor contains the complete result.

These examples use the same owning compiler, typed result branches and proved
semantic interface. The native adapters select a model explicitly and remain
handwritten local tooling. General disjunction/existential proofs, induction,
recursive or higher-order functions, local prop/function definitions and
nested theorem definitions are separate extensions.

The selected slice passed its combined phases 8-12 checkpoint on 2026-10-11.
The gate checks 74 actual source/generated pairs, including 19 new mathematical
cross-cases, and 64 interfaces in each native layer. An ordinary pinned Lake
client imports only `native.Final` and checks 64 direct applications plus six
combinations. Live dependency audits connect native proofs to their intended
generated declarations after beta/zeta reduction; unused citations do not count.
The local completion matrix distinguishes whole-file checking, selected result
stages and actual native statements. Among the 19 new interfaces, ten are closed,
six generic and three mixed. The natural-output property and additional local
declaration statements are checked in their generated files without separate
native exports. These checks establish the reviewed subset, not every proof
route that Litex can verify. All tooling and acceptance evidence remain local
under `scripts/litex_to_lean/`.

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
