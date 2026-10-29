# Litex-to-Lean Compiler Guide

This guide explains the design principles of Litex-to-Lean compilation through
concrete source/generated examples. It is the maintained entry point for why
the compiler works this way and what its output means.

To see the implemented work directly, follow the [example reading path](#explore-the-example-collection)
and browse the [complete source/generated collection](../lean/examples/).

The [compiler README](../src/compile_to_lean/README.md) explains the Runtime-to-native
architecture, typed-result ownership, Core semantics and the native interface
boundary. This guide covers user-facing design principles and detailed use;
complete worked examples live in their own READMEs. [CLI documentation](cli.md#lean-compiler-boundary)
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

The [proof-command checkpoint](Litex_To_Lean_Proof_Commands.md) adds paired examples for compound contradiction, set/function extensionality, strong induction, finite enumeration and midpoint geometry. It records the checked scope and each adapter's current domain boundaries.

## Explore the example collection

For the shortest complete source/generated/Adapter/Final walkthrough, start
with the [adding-zero README](examples/litex_to_lean/add_zero/README.md).
The [Newton README](examples/litex_to_lean/newton_residual/README.md) then adds a
function whose nonzero domain condition survives compilation and native use.

The [complete collection](../lean/examples/) contains dozens of Litex `.lit`
files paired with the `.lean` files produced by the compiler. The 2026-10-12
acceptance checkpoint checked 74 pairs through strict source verification,
actual compilation, byte-for-byte regeneration and pinned Lean/Mathlib
checking. The collection continues to grow beyond that dated checkpoint;
explore the maintained examples through this progression, opening both files
in each row:

| Mathematical step | Litex source | Generated Lean | What to inspect |
|---|---|---|---|
| Exact fractions and decimals | [Source](../lean/examples/exact_fractions_and_decimals/statement.lit) | [Lean](../lean/examples/exact_fractions_and_decimals/statement.lean) | Exact arithmetic and the distinction between `1 / 3` and `0.333`. |
| A reciprocal with a domain condition | [Source](../lean/examples/guarded_real_reciprocal/statement.lit) | [Lean](../lean/examples/guarded_real_reciprocal/statement.lean) | The function definition, evaluation at two and preserved nonzero premise. |
| The closed unit interval | [Source](../lean/examples/closed_unit_interval/statement.lit) | [Lean](../lean/examples/closed_unit_interval/statement.lean) | A bounded set builder, membership and the bounds known for each member. |
| Reusing a theorem's conclusions | [Source](../lean/examples/named_compound_theorem_returns/statement.lit) | [Lean](../lean/examples/named_compound_theorem_returns/statement.lean) | Multiple returned facts and explicit selection in subsequent proofs. |
| Two rational inverse maps | [Source](../lean/examples/rational_inverse_maps/statement.lit) | [Lean](../lean/examples/rational_inverse_maps/statement.lean) | Definitions, domain preservation, both inverse laws and injectivity in one development. |

Compare each source's mathematical statements and intermediate facts with the
generated theorem's premises and proof references. The collection records the
compiler's development in inspectable form, across arithmetic, object
construction, definitions and proof reuse. The [acceptance discussion](#what-successful-output-establishes)
explains how to read the dated checks and their scope; the later rational-map
walkthrough follows the last example through a native Mathlib interface.

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

Completed object registrations are also reusable inside `witness`, `by cases`
and `by contra`; their names remain local to those blocks. For Cartesian
parameters, numeric observations consume the already emitted coordinate
objects and membership facts. Arithmetic observations read their recorded
child WD results directly.

Function applications also share completed argument WD within the current
candidate check. `FnObjDomainCheckResult` retains the ordered checks and their
local environment; `formed_children` records each producing child index and
its WD ID. After a compound argument succeeds, later checks can cite it with
`ByKnown`. For example, checking `dot(vec(a,b), vec(a,b))` can construct
`vec(a,b)` once and cite that construction for the second argument and both
membership-subject WD checks. Membership and guard proofs are still checked.

The compiler emits that child once as `_object_w<ID>` and resolves later
citations through the original result scope. Missing registrations, mismatched
subjects and references to unfinished children reject compilation. Failed
function candidates retain their diagnostic scope without publishing its
registrations to the caller. This sharing comes from the producing result;
the compiler has no additional object cache.

An object's constructor can depend on a local membership or nonzero proof.
If its exported proposition uses that proof name, the generated type includes
the necessary original `let` and `have` declarations in a `by` expression,
ending with `exact <proposition>`. Lean completes each producer before
elaborating the next one. This avoids repeatedly copying unresolved proof
dependencies across nested term bindings. The proved facts remain internal
definitions, not additional theorem assumptions.

Local typed facts use `litex_checked_step` to turn the generated proof into a
kernel-checked auxiliary theorem. Its closure retains the local object values
and WD definitions (`mkAuxTheorem` with `zetaDelta := true`), so later facts can
reference the checked proof. This helper does not search for a proof, and it
rejects open goals. Exported theorems and direct projection citations keep
their existing declaration forms.

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
predicates, with the exact recorded membership/subset routes. General disjunctive
filters, finite binder kinds, standalone `have A nonempty_set`, unbounded
comprehension and existence-based set selection remain outside this bounded-builder
slice. Unsupported routes do not become axioms. These restrictions concern the
builder routes above. Other set operations have supported evidence routes, such
as [difference and power-set monotonicity](../lean/examples/set_containment_monotonicity/).

## Structures and field dependencies

```litex
struct CoordinatePair:
    x R
    y R

forall p &CoordinatePair:
    p.x = p(1)
    p.y = p(2)
```

`&CoordinatePair` compiles to the existing Cartesian set wrapper. The parameter
`p` remains a generic certified object with a membership premise. Its field
names select coordinates of the finite function; `p.x` uses `Litex.cartCall`
with that premise. The compiler replays the automatically opened Cartesian
membership, field equalities and field memberships under their original IDs.
The [full example](../lean/examples/coordinate_pair_fields/) also uses both
coordinates in real arithmetic.

Fields may use distinct carriers, as in an [indexed point](../lean/examples/indexed_point_fields/),
or a [previously declared arbitrary set](../lean/examples/arbitrary_carrier_pairs/).
[Nested tuple membership](../lean/examples/nested_coordinate_membership/)
first proves the inner pair's membership and then cites it for the outer
structure. These are independent field carriers.

The same representation supports named objects and explicit opening:

```litex
witness $is_nonempty_set(&CoordinatePair) from (1, 2)
have p &CoordinatePair
release struct def p
p.x $in R

have origin &CoordinatePair = (0, 0)
origin.x = 0
```

The first declaration consumes its actual nonempty proof. The second checks
the original type preflight, value WD and membership before emitting the alias
and its field facts. Original FactIds are retained throughout.
See [chosen pairs](../lean/examples/chosen_coordinate_fields/),
[the origin](../lean/examples/origin_coordinate_fields/),
[explicit release](../lean/examples/released_coordinate_fields/),
[local declarations](../lean/examples/local_coordinate_objects/) and
[a theorem using release](../lean/examples/coordinate_field_theorem/).
[Two-pair arithmetic](../lean/examples/coordinate_pair_addition/) also exercises
ordered automatic opening of multiple parameters.
Defining conditions restrict the Cartesian carrier:

```litex
struct PositivePoint:
    x R
    y R
    <=>:
        x > 0

(2, 3) $in &PositivePoint
forall p &PositivePoint:
    p.x > 0
```

The generated carrier uses `Litex.setBuilder`. Membership supplies the field
memberships and defining inequality; opening the structure projects those
proofs under their original FactIds. The [positive-point pair](../lean/examples/positive_point_conditions/)
also proves membership of an arbitrary Cartesian pair from a positive first
coordinate. [Ordinary and local choice](../lean/examples/chosen_positive_points/)
and [explicit release](../lean/examples/positive_point_release/) retain the condition.

Conditions are checked in order. In the [positive-ratio pair](../lean/examples/positive_ratio_conditions/),
`denominator != 0` supplies WD for the following `numerator / denominator > 0`.
[Equality](../lean/examples/equal_coordinate_conditions/),
[flat conjunction](../lean/examples/first_quadrant_conditions/) and
[chain conditions](../lean/examples/ordered_coordinate_conditions/) have paired examples.
The compiler uses existing set-builder laws and preserves the original
published universal laws; no additional semantic assumption is introduced.

Header parameters define reusable carrier families:

```litex
struct Pair<A set>:
    x A
    y A

forall A set, p &Pair<A>:
    p.x $in A
    p.y $in A
```

`A` remains a certified generic object with an ordinary sethood fact. The
generated family takes that object and proof; specialization consumes the
recorded argument WD and type proofs. It does not specialize the declaration
to a native numeric host type. The [generic pair](../lean/examples/parameterized_pairs/)
and [parameterized diagonal](../lean/examples/parameterized_equal_pairs/) demonstrate
arbitrary set arguments. A [real threshold](../lean/examples/threshold_points/)
can occur in a condition, and [a designated coordinate](../lean/examples/designated_coordinate_pairs/)
uses `A set, a A`: later header parameters can depend on earlier ones.
[Global/local declarations and release](../lean/examples/chosen_parameterized_pairs/)
preserve the instantiated fields.

`A nonempty_set` is also accepted in structure headers and universal/theorem
parameters. It becomes a generic object plus its original `Litex.IsNonempty`
fact, without choosing an element. Specialization requires an actual proof of
nonemptiness. See [nonempty pairs](../lean/examples/nonempty_parameterized_pairs/),
[their defining equality](../lean/examples/nonempty_equal_pairs/) and
[a reusable theorem on nonempty Cartesian products](../lean/examples/nonempty_cartesian_theorem/).

Later fields can depend on earlier ones:

```litex
struct RepeatedCoordinate:
    x R
    y {x}

forall p &RepeatedCoordinate:
    p.y $in {p.x}
    p.y = p.x
```

The [generated pair](../lean/examples/repeated_coordinate_fields/) represents
the carrier as a `Litex.DependentFields` family. Its formation proof consumes
the original field WD and parameter inferences in declaration order.
`Litex.dependentCart` collects exactly the flat tuples satisfying those field
memberships. The object `p` retains its generic representation and ordinary
membership premise. Opening it produces the original Cartesian and field facts
under their recorded FactIds.

This construction requires the optional `IndexedUnionSemantics M` interface,
whose set-indexed union laws are proved for the existing ZF-based `NumericModel`.
The compiler adds that requirement to files declaring dependent fields.
Independent structures keep their existing `SetSemantics`/`FunctionSemantics`
requirements. No project axiom is added.

The same route handles [a member of a member](../lean/examples/member_coordinate_pairs/)
(`x A; y x`), [three dependent fields](../lean/examples/repeated_coordinate_triples/),
[a positive defining condition](../lean/examples/positive_repeated_coordinates/),
[membership from an existing Cartesian pair](../lean/examples/equal_coordinates_membership/)
and [choice, explicit release and local aliases](../lean/examples/chosen_repeated_coordinates/).
In [the reciprocal example](../lean/examples/reciprocal_coordinate_fields/),
`x R+; y {1 / x}` uses the first field's stored nonzero inference to construct
the second carrier. Released carriers reuse the declaration's formation proof.

The slice requires at least two fields. Field dependencies must point backward
in declaration order. Finite-set header kinds, quantified conditions, nested
field paths, function-call receivers and local/qualified structure definitions
remain outside this slice. Field access and release use directly declared
structure parameters or typed aliases.

## Formula functions and concrete predicates

Top-level abstract predicates also compile. This source preserves a property
when an object is replaced by an equal one:

```litex
abstract_prop marked(x)
forall a, b R:
    a = b
    $marked(a)
    =>:
        $marked(b)
```

The declaration becomes a parameter
`(abstract_prop_1 : (Fin 1 → M.Value) → Prop)`; each call applies it to the
argument's denotation. The proof uses the recorded equality and property
citation. No truth is assumed merely by declaring the predicate.
See the [source and generated proof](../lean/examples/abstract_property_transport/),
[binary relation and negation](../lean/examples/abstract_relation_transport/),
[nullary proposition](../lean/examples/abstract_proposition_identity/) and
[abstract function guard](../lean/examples/abstract_function_guard/).
Local and qualified abstract declarations remain unsupported.

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

The current formula slice supports one or two fixed N/Z/Q/R/C inputs and output,
with the reviewed `R+` input and target extension,
numeric RHS/let carrier aliases, direct and concrete-predicate function guards,
and top-level concrete predicates with atomic or flat And/chain
defining clauses. [Nonnegativity](../lean/examples/nonnegative_real_property/statement.lit)
demonstrates predicate definition and unfolding; [quotient distribution](../lean/examples/real_quotient_distributes/statement.lit)
demonstrates two arguments. The
[composed formula](../lean/examples/composed_real_formula/statement.lit) calls
earlier one/two-input functions in its body, while the
[chain guard](../lean/examples/chain_guard_reciprocal/statement.lit) retains a
concrete predicate's two inequalities before constructing the reciprocal.
The bounded unary-natural recursive graph slice and ordinary zero-based
induction are described in the [compiler README](../src/compile_to_lean/README.md).
A [verified single-step Newton example](#verified-single-step-newton-example)
appears below.
Higher-order bodies and recursion outside that slice remain unsupported.

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

The [nonzero difference](../lean/examples/nonzero_real_difference/statement.lit)
example compiles `x != 1 => x - 1 != 0` through the original selected
`DiffNonzeroFromInequality` result. Its exact operand inequality and numeric
domain evidence feed the proved `Litex.subNonzeroOfNotSame` law. This route
also supports generic complex members, either zero orientation and certified
closed zero expressions. Missing or changed premise evidence remains rejected;
this does not add support for other nonzero builtin families.

The [real Möbius involution](../lean/examples/real_mobius_involution/statement.lit)
now combines difference and quotient nonzero proofs, a known nonzero-difference
citation, and original forall applications. Its map `(x+1)/(x-1)` preserves
`x != 1` and applying it twice returns `x`. The compiler consumes the recorded
numerator/denominator proofs and exact argument/type/domain evidence, including
the nested call's domain check. Supported non-equality atomic forall conclusions
share the existing Chain/And consumer; this does not enable every equality,
compound conclusion or higher-order application route.
The [native consumer](../showcases/litex_to_lean_adapter/Final.lean) obtains the
ordinary real theorem through a handwritten, proved representation adapter.

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

When storing an atomic fact registers a new object as well-defined,
`StoreFactAndInferResult.formed_subjects` retains its original argument index
and WD ID. The compiler connects that registration to the argument's checked
construction and emits `_object_w<ID>` once. Later facts in the same source
scope can reference that definition. Numeric literals keep their native
constructors. Nested WD children can also share local Lean `let` bindings.
These references reduce repeated construction terms without changing the
selected proof or introducing new assumptions. The compiler reads registrations
from preceding result records; it does not search the verifier again.

A child does not need its own Runtime WD registration to be reused. After
`$is_set((a + 1) * (a + 2))`, a later `$is_set(a + 1)` can take the certified
left operand from the stored product's `.val.left`. The later result may still
contain an independent `ByDef` proof. The compiler validates that proof's own
construction conditions, then uses the earlier projection when the object and
its Lean representation match. Function calls must also retain the same
selected signature citation. Only preceding, visible constructors qualify;
children built inside a closed proof cannot escape it. This uses the existing
result tree and source-position lookup, without adding a Runtime cache.

The equality store for `have points set = cart(R, R)` also registers the
right-hand object's WD. Later uses of `cart(R, R)` reuse the declaration's
`_object_i<ID>`, which already contains its value and WD proof. The compiler
checks the original registration and source scope before citing it; a
declaration inside a proof remains local to that proof.

Concrete `prop` clauses retain the same registrations in
`AssumeDomFactResult.store_and_infer.formed_subjects`, alongside their original
`well_defined` evidence. The compiler emits those constructors before each
clause's proof binder and reuses their WD IDs in later clauses. For example,
the two bounds below share one addition object:

```litex
prop shifted_interval(x R):
    x + 1 >= 0
    x + 1 <= 2
```

These local definitions do not escape the predicate.
This uses existing result fields; no additional Runtime cache is involved.

Compact output needs references to earlier evidence, not just more detailed
proof trees. Some arithmetic WD requirements still check an operand again
after checking it as a child, retaining another construction subtree. That
producer path remains a separate source of duplication. The compiler does not
yet promise 10–20 Lean lines for every source statement; nested definitions and
proof blocks can still produce substantially larger declarations.

Named formula calls can project the signature already stored in the function
object when the original membership ID and signature match its declaration.
An output-membership proof can likewise reuse an emitted call. A separately
checked occurrence qualifies when it has the same source application, exact
signature citation and compatible child constructors. The compiler validates
that occurrence's own argument, domain and return evidence before choosing the
existing binding. For example, the membership proof needed to square `f(x)`
can refer to `let _litex_return_call := _wd_1_0` instead of emitting another
`Litex.call` with the same arguments. Different signatures and arithmetic
constructor variants are not interchangeable. This reduces generated terms;
it does not remove duplicate subtrees from the Runtime result.

Looking back at a completed statement's WD result retains its emitted object
bindings. The original construction's fact prefix stays unchanged: replay may
reuse the object, but cannot cite that statement's own conclusion or later facts
to justify its construction. A completion boundary also prevents a pending
statement from borrowing these bindings through an enclosing completed cursor.

For chains and conjunctions, each child compilation returns its proposition and
proof together. The enclosing result assembles those pairs instead of rebuilding
the propositions from their source objects. Numeric bridge applications let Lean
infer scalar arguments already determined by the child certificates; they do not
copy the same scalar expression into every parent certificate.

The same rule applies inside a constructed object. For example, once a power
object has been emitted, its checked base is available as `power.val.base`.
The compiler follows the original WD children through fields that retain their
host objects, rather than reconstructing the base and its domain evidence.
It does not use this shortcut for tuple factors: tuple representations retain
denotations, not the original child host objects.

Calls likewise retain their original argument objects. Numeric calls expose
`argument`, or `first` and `second`; generic two-argument calls use
`CallArguments2` inside the call's `argument` field. Its denotation is
definitionally the same tuple of the two argument denotations. Keeping the
objects allows later replay to project their original WD. Three-argument
generic packing still retains only denotations.

The stored WD proof is reusable too: an emitted addition object supplies its
two original domain proofs as `object.wd.1` and `object.wd.2`. The compiler uses
these projections only for the exact requirement node of a completed original
constructor. Equal propositions from another result do not qualify. Division
keeps the verifier's guard-first order when mapping to its wrapper's proof fields.

Cartesian coordinate inference already records each conclusion's FactId.
Its output binds the coordinate as `_object_h<ID>` before emitting `h_<ID>`;
later uses resolve that original producer. This needs no additional result
field. In contrast, `formed_subjects` captures WD IDs which storage previously
allocated without returning them. Both mechanisms use source-owned identities,
not a compiler-owned cache.

The [point reconstruction example](../lean/examples/point_from_coordinates/statement.lit)
compiles `p = (p(1), p(2))` using `FiniteFunction.reconstruct`. Its recorded
Cartesian membership supplies the dimension, and each recorded receiver
equality supplies the corresponding coordinate. The generated proof normalizes
the fixed `Fin n` index to the source's one-based numeral. The
[generated Lean](../lean/examples/point_from_coordinates/statement.lean) has
passed Lean checking, as have reversed three-dimensional reconstruction and
coordinates transported through an original `p = q` fact.

Fixed representation conversions and domain assembly belong in proved Core
lemmas. `callArguments2_mem_cart` consumes the two original argument-membership
proofs and infers their carriers, avoiding another copy of the carrier objects
and the finite-vector proof at each call. For example,
a coordinate call passes its original closed-range membership proof to
`Litex.indexSetMemberOfClosedRange`, rather than repeating the range constructor
and its conversion proof. Literal membership uses `numberInZOfEq` and the
corresponding numeric bridges directly. Literal range certificates retain the
source's complex payloads and their checked integer representatives through
`numberInClosedRangeOfEq`; composite expressions retain their denotation
certificates.

When an original Cartesian membership already determines the coordinate call's
carrier, Lean infers that carrier from the citation instead of receiving another
copy of its constructor. `FiniteFunction.coordinate_mem_number` applies the
recorded coordinate inference to the exact source numeral.

Object-producing bindings use Lean term-level `let`s so that their values
remain available to subsequent field projections. Proof arguments still come
from the recorded verification steps. Sharing these constructors and citations
reduces the output while preserving the checked proof route.

`Litex.SelectedFn` supplies the semantic construction for a function specified
by unique existence. Its payload contains a `FunctionSignature` and an output
predicate; its WD proof establishes exactly one output for every input in the
declared domain. The denotation is a set-theoretic function graph, independent
of the supplied WD proof. No output inhabitant is required outside the domain.

`existsUniqueValueOfObjects` converts canonical Litex witnesses and pairwise
`Same` uniqueness to uniqueness of their denotations. `selectedFn_call_spec`
proves that a call satisfies the output predicate, and `selectedFn_unique`
identifies any other admissible output with that call. These laws follow from
the existing `FunctionSemantics` interface without new model fields or axioms.
The compiler consumes `have fn … by exist!` through
`compile_have_fn_by_exist_result.rs`. It replays `source_forall` and
`fn_set_well_defined`, constructs the function, then publishes the captured
membership, property and uniqueness facts under their original FactIds.
`property_well_defined` supplies the original input bindings and constructors
when a later call reuses the property. No second proof search or function
registry is introduced. Local declarations and unsupported function signatures
still reject explicitly.

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
retains its own evidence and calls a proved Core law. Each inference stores
its direct conclusion without another inference pass. Nested cancellation
records an explicit intermediate source step and then that step's own result:

```litex
thm cancel_nested:
    ? forall a,b,x,y Q:
        x!=0
        y!=0
        (a*x)*y=(b*x)*y
        =>:
            a=b
    a*x=b*x
    a=b
```

The compiler replays both actual producers in order. Removing a
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

For a Litex-only check, the Rust verifier, builtin rules and inference rules
remain in the trusted computing base (TCB). When a generated proof passes
independent Lean checking with the intended axiom boundary, Lean establishes
the generated theorem under its explicit hypotheses. Its proof validity does
not depend on accepting the Rust verifier's success report. The separate
question is whether that theorem faithfully expresses the intended Litex
statement: object meanings, premises, construction conditions and scope still
need review. [Lean's proof-validation guide](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
explains the distinction between a valid proof and its statement's meaning.

The compiled examples provide evidence for reviewed mappings; they do not
prove every Rust verifier branch sound. Readers can inspect the design through
[How Litex works](https://litexlang.com/how-litex-works), the source/generated
examples in this guide and the proved bridges in [the Lean semantic interface](../lean/Litex.lean).
These make the current contracts and assumptions available for review.

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

The handwritten Adapter selects a model and proves the representation
conversions. These can be reused across a development; clients call ordinary
theorems such as `Adapter.realQuotientDistributes`. A new mathematical domain
may need additional conversions. Automatic generation of these Mathlib
interfaces remains future work.

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

The acceptance counts in this guide refer to dated local checks, with a fixed
Lean/Mathlib environment. The semantic interface and source/generated pairs
are public; the check driver and receipts remain in the local-only workspace.
These are local check records, not release/tag CI results.

The interpretation of an arbitrary set illustrates a deliberate interface
difference: `$is_set(A)` has a generated proof, while native `A : ZFSet`
already expresses sethood through its type. No artificial native sethood
predicate is needed. Numeric views of a whole set still need subset evidence.
The selected slice leaves modules, general existential witness declarations,
unbounded comprehension, existence-based set choice, higher-order bodies and
recursion outside the reviewed unary-natural slice
and unsupported inference/certificate routes outside the compiler boundary.
An observed unused inference node in a result trace does not establish
compiler support for that inference.

The long-term goal is to extend replay to the remaining Litex proof routes.
Each extension must preserve the source meaning, consume its recorded
evidence, and pass Lean checking.

## Two rational maps, from definitions to a native equivalence

The [rational inverse maps source](../lean/examples/rational_inverse_maps/statement.lit)
develops one connected argument. The map
\(f(x)=(2x+1)/(x-1)\) sends \(\mathbb{Q}\setminus\{1\}\) into
\(\mathbb{Q}\setminus\{2\}\); its inverse is
\(g(y)=(y+1)/(y-2)\). The source defines both functions, proves that their
values lie in the required domains, proves both inverse laws, and uses an
inverse law to establish injectivity. Its
[generated Lean file](../lean/examples/rational_inverse_maps/statement.lean)
preserves the evidence for that whole argument.

The source definitions put each excluded value in the function's domain:

```litex
have fn forward(x Q:x!=1) Q=(2*x+1)/(x-1)
have fn backward(y Q:y!=2) Q=(y+1)/(y-2)
```

The full source first establishes the elementary nonzero facts needed by
these quotients. The first domain theorem then gives the mathematical reason
why a later call to `backward(forward(x))` is legal:

<!-- litex:skip-test -->
```litex
thm forward_preserves_domain:
    ? forall x Q:
        x!=1
        =>:
            forward(x)!=2
    forward(x)=(2*x+1)/(x-1)
    forward(x)-2=3/(x-1)
    3/(x-1)!=0
```

The corresponding theorem for `backward` excludes 1. With both domain facts
available, the source checks the rational identities
`backward(forward(x))=x` and `forward(backward(y))=y`. These are proved named
theorems, so the final injectivity argument can reuse them. Under
`a!=1`, `b!=1` and `forward(a)=forward(b)`, it selects these two results:

<!-- litex:skip-test -->
```litex
by thm backward_forward(a) => backward(forward(a))=a
by thm backward_forward(b) => backward(forward(b))=b
```

Each invocation returns typed evidence for the selected equality, its
argument membership and its domain conditions. Compilation follows those
results and their original FactIds, naming source proof declarations and
references `h_<FactId>`. In particular, a nested `Litex.call` must receive the
proof that the inner function value satisfies the outer function's domain.
The compiler resolves the recorded proof; the generated call does not acquire
an extra unproved hypothesis. The rational-identity proof similarly retains
the selected normalization route and its nonzero denominator evidence.

The five exported proofs in the linked generated file have these source IDs;
all belong to its source-path namespace:

| Source theorem | Generated declaration |
|---|---|
| `forward_preserves_domain` | `h_1042` |
| `backward_preserves_domain` | `h_5990` |
| `backward_forward` | `h_10318` |
| `forward_backward` | `h_21048` |
| `forward_injective` | `h_37256` |

The public companion files show how this result reaches a Mathlib user.
[RationalMaps.lean](examples/litex_to_lean/rational_inverse_maps/RationalMaps.lean)
defines the ordinary functions on `ℚ`.
[Adapter.lean](examples/litex_to_lean/rational_inverse_maps/Adapter.lean)
chooses `Litex.NumericModel.model`, encodes rational inputs and premises,
consumes the generated theorems, and observes their function values through
the proved function and numeric representation laws. This handwritten layer
proves the representation conversion; it uses the generated proofs for the
domain, inverse and injectivity conclusions.
[Final.lean](examples/litex_to_lean/rational_inverse_maps/Final.lean) exposes
ordinary rational statements and packages the two inverse laws as an `Equiv`:

```lean
namespace RationalMaps
def equivalence : {x : ℚ // x ≠ 1} ≃ {y : ℚ // y ≠ 2} where
  toFun x := ⟨forward x, forwardPreservesDomain x x.property⟩
  invFun y := ⟨backward y, backwardPreservesDomain y y.property⟩
  left_inv x := Subtype.ext (leftInverse x x.property)
  right_inv y := Subtype.ext (rightInverse y y.property)
end RationalMaps
```

Here each subtype contains an ordinary rational and the proof that it avoids
the excluded value. Domain preservation constructs the output subtype, and
the two inverse laws supply the `Equiv` fields. A client imports
`rational_inverse_maps.Final`; the
[ordinary client](examples/litex_to_lean/rational_inverse_maps/UseInYourProject.lean)
uses this native interface. Its theorem statements need no Litex objects or
semantic parameters.

To use these files in a Mathlib project preserving the repository's directory
layout, add the following library entries to its `lakefile.toml`. The checked
example uses Lean 4.31.0 and Mathlib commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

```toml
[[lean_lib]]
name = "Litex"
srcDir = "lean"
roots = ["Litex", "examples.rational_inverse_maps.statement"]

[[lean_lib]]
name = "CompilerDocExamples"
srcDir = "docs/examples/litex_to_lean"
roots = ["rational_inverse_maps.UseInYourProject", "rational_inverse_maps.DirectLean"]
```

Run `lake build CompilerDocExamples`; subsequent files can import
`rational_inverse_maps.Final`. Regenerate the source pair from the repository
root with the actual compiler:

```sh
target/release/litex -strict -lang en -f lean/examples/rational_inverse_maps/statement.lit
target/release/litex -strict -lean -f lean/examples/rational_inverse_maps/statement.lit > lean/examples/rational_inverse_maps/statement.lean
```

The final injectivity proof lists nonzero facts and expands the formulas
explicitly. A shorter equality chain using function congruence can pass Litex
verification but select a route the current Lean compiler does not support.
The [direct Mathlib version](examples/litex_to_lean/rational_inverse_maps/DirectLean.lean)
proves the same result without the compilation and Adapter steps.

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
An ordinary natural parameter's recorded nonnegative inference is emitted once,
with its own FactId. A natural membership projected from a predicate or builder
is stored without another inference pass. A later explicit membership statement
can start its own single-hop inference. Predicate and bounded-builder clauses
can reuse literal WD from completed parameter inference. A pending inference still cannot cite its own
future fact, even if an ancestor contains the complete result.

These examples use the same owning compiler, typed result branches and proved
semantic interface. The native adapters select a model explicitly and are
handwritten. Public worked examples keep Adapter/Final under
`docs/examples/litex_to_lean/`; verification tooling and receipts stay local.
The compiler now also consumes the reviewed
natural-index coverage disjunction, unary-natural recursive graphs and
ordinary zero-based induction. General existential proofs, disjunction and
induction outside those reviewed routes, higher-order functions, local
prop/function definitions and nested theorem definitions remain separate
extensions.

The original phases 8-11 minimum passed fresh acceptance on current single-hop
typed results on 2026-10-12. The checkpoint checks 74 actual source/generated
pairs, including 19 mathematical cross-cases, 45 maintained profiles and six
separate whole-known Chain/And and WD-factory profiles. It also checks 64
interfaces in each native layer. An ordinary pinned Lake
client imports only `native.Final` and checks 64 direct applications plus six
combinations. Live dependency audits connect native proofs to their intended
generated declarations after beta/zeta reduction; unused citations do not count.
The local completion matrix distinguishes whole-file checking, selected result
stages and actual native statements. Among the 19 new interfaces, ten are closed,
six generic and three mixed. The natural-output property and additional local
declaration statements are checked in their generated files without separate
native exports. These checks establish the reviewed subset, not every proof
route that Litex can verify. Current acceptance_phase8_current through
acceptance_phase11_current and acceptance_phases8_11_current receipts bind the
exact source/result/build evidence. The 2026-10-11 phases 8-12 receipts remain
historical. All tooling and acceptance evidence remain local under
`scripts/litex_to_lean/`.

## Verified single-step Newton example

The [Newton README](examples/litex_to_lean/newton_residual/README.md) contains the
complete source, generated-proof explanation and ordinary Lean consumer for
`((x + 2/x)/2)^2 - 2 = ((x - 2/x)/2)^2` with `x ≠ 0`. The single-step identity
and positive-update variant have checked Adapter/Final layers that consume
the actual generated proofs.

The same README records the separate recursive all-index example. Its generated
proof passed full Lean checking on 2026-10-21 with a 2000000-heartbeat budget,
above Lean's default 200000. The native all-index interface is still unfinished.

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

## Current mathematical coverage and examples

**Litex has established the source-proof → generated-Lean → Lean-checking path
for a concrete mathematical subset: elementary algebra and inequalities over
the standard number systems, together with basic sets, functions with explicit
domains and reusable theorems.** These capabilities combine in proofs with
arbitrary parameters, hypotheses and intermediate steps. Selected complete
examples also expose ordinary Lean/Mathlib theorems through handwritten adapters.

| Mathematical layer | Current coverage | Corresponding examples |
| --- | --- | --- |
| Numbers | ℕ, ℤ, ℚ, ℝ, ℂ and the supported positive, negative and nonzero subsets: all 15 source number sets are represented; parameters retain their original host representations. | [Numeric hierarchy](../lean/examples/numeric_hierarchy/), [signed/nonzero domains](../lean/examples/signed_numeric_domains/), [subset statements](../lean/examples/signed_numeric_subsets/) |
| Operations and relations | Exact fractions and finite decimals, four arithmetic operations, polynomial and rational identities, cancellation; selected fixed integer powers and real inequalities. | [Fractions and decimals](../lean/examples/exact_fractions_and_decimals/), [difference of squares](../lean/examples/real_difference_of_squares/), [cancellation](../lean/examples/multiplicative_cancellation/), [nonnegative squares](../lean/examples/real_squares_nonnegative/) |
| Sets | Arbitrary set parameters, empty sets, finite enumerations, bounded set builders, membership, subsets and associated reasoning. | [Arbitrary sets](../lean/examples/arbitrary_set_laws/), [finite sets](../lean/examples/finite_natural_set/), [closed unit interval](../lean/examples/closed_unit_interval/) |
| Functions | Formula functions with one or two numeric parameters, explicit domain conditions, evaluation and composition; complete inverse and injectivity examples. | [Guarded two-argument function](../lean/examples/two_argument_shifted_quotient/), [composition](../lean/examples/composed_real_formula/), [rational inverse maps](../lean/examples/rational_inverse_maps/) |
| Finite aggregation | Sums/products on explicit domains; ordered `reduce` and unordered `finite_set_reduce`, retaining input, operation and initial-value WD. | [Explicit domains](../lean/examples/general_finite_aggregate_closure/), [ordered subtraction](../lean/examples/ordered_subtraction_fold/), [finite fold](../lean/examples/finite_fold_carrier/) |
| Hyperbolic functions | `sinh`, `cosh`, `tanh`, `coth`, `sech`, `csch`, with domains, basic values and selected defining identities. | [Domains](../lean/examples/hyperbolic_domains/), [definitions](../lean/examples/hyperbolic_definitions/), [identities](../lean/examples/hyperbolic_identities/) |
| Finite linear algebra | Matrix spaces, zero/identity matrices, transposes, entrywise operations, scalar/matrix multiplication, natural matrix powers, deleted-row/column matrices, cofactors, adjugates and inverses with nonzero-determinant WD, vector application, diagonal/outer products, trace, determinant, rank, inner product and vector/matrix norms; selected carrier, definition and nonnegativity proofs. | [Matrix product](../lean/examples/matrix_multiplication/), [coordinate formula](../lean/examples/matrix_multiplication_coordinates/), [matrix powers](../lean/examples/matrix_power_membership/), [deleted-row/column coordinates](../lean/examples/matrix_minor_coordinates/), [cofactors](../lean/examples/matrix_cofactor_small_orders/), [adjugate coordinates and computation](../lean/examples/matrix_adjugate_two_steps/), [guarded inverse theorem](../lean/examples/matrix_inverse_theorem/), [rank bounds and theorem reuse](../lean/examples/matrix_rank_bounds/), [successor power](../lean/examples/matrix_power_successor/), [vector application](../lean/examples/matrix_vector_definition/), [determinant laws](../lean/examples/matrix_determinant_transpose/), [small-order determinants](../lean/examples/matrix_determinant_small_orders/), [inner product](../lean/examples/finite_inner_product_definition/), [vector norm](../lean/examples/euclidean_norm_nonnegative/), [matrix norm](../lean/examples/frobenius_norm_nonnegative/) |
| Real-set bounds | Upper/lower bounds and one-/two-sided boundedness, with their negations; original real-domain WD, definition folding/unfolding, witnesses, citations, equality transport and theorem reuse. Core bridges connect these to Mathlib bounds and boundedness. | [Bound theorem](../lean/examples/real_set_bound_theorem/), [empty set](../lean/examples/real_empty_set_bounds/), [witnesses and components](../lean/examples/real_set_bounded_components/), [predicate citations](../lean/examples/real_set_bound_citations/) |
| Real extrema | `sup(A)` and `inf(A)` with recorded carrier and selection evidence; certificate definition, existence, uniqueness, bound/member comparisons and crossing witnesses; citations, substitution and formula-function bodies. | [Supremum laws](../lean/examples/real_supremum_certificate_laws/), [infimum laws](../lean/examples/real_infimum_certificate_laws/), [candidate theorem and aliases](../lean/examples/real_supremum_candidate/), [functions](../lean/examples/real_extremum_functions/) |
| Real sequences | Monotonicity and boundedness; Cauchy, convergence and a specified real limit. Includes definition replay, inferred witnesses, positive/negative citations, equality transport and named theorem calls. Exact unary `N+ → R` domains without extra guards; `lim` consumes recorded convergence evidence and supports selected-value equality and uniqueness for suitably typed parameters; `limsup` and `liminf` selectors remain pending. | [Monotonicity](../lean/examples/sequence_monotonicity/), [range and bounds](../lean/examples/sequence_range_bounds/), [Cauchy tails](../lean/examples/sequence_cauchy_definition/), [epsilon-limit definition](../lean/examples/sequence_limit_definition/), [convergence witnesses](../lean/examples/sequence_convergence_witness/), [limit citations](../lean/examples/sequence_limit_citations/) |
| Structures | Top-level set/nonempty-set/object header parameters, independent or ordered dependent fields, atomic/flat conjunction/chain conditions, tuple membership, quantified and declared objects, typed aliases, explicit release, direct field access and numeric field arithmetic; arbitrary carriers and nested tuple instances. | [Generic pairs](../lean/examples/parameterized_pairs/), [dependent coordinates](../lean/examples/repeated_coordinate_fields/), [member pairs](../lean/examples/member_coordinate_pairs/), [reciprocal fields](../lean/examples/reciprocal_coordinate_fields/), [positive points](../lean/examples/positive_point_conditions/) |
| Definitions and proofs | Concrete predicates, top-level abstract predicates, universal and conditional facts, equality chains, selected conjunctions, named theorems and calls, local objects, `let`, `claim` and `sketch`. | [Abstract properties](../lean/examples/abstract_property_transport/), [predicate equality transport](../lean/examples/concrete_predicate_equality_transport/), [theorem returns and calls](../lean/examples/named_compound_theorem_returns/), [local objects](../lean/examples/local_witness_additive_identity/), [claim and positive return domain](../lean/examples/newton_positive_update/) |

`sketch:` checks its body in a discarded scope. The compiler replays every child
result inside a private Lean proof block, retaining outer citations and original
WD IDs. It publishes no source facts from that block. See [local arithmetic](../lean/examples/local_arithmetic_sketch/),
[nested blocks](../lean/examples/nested_arithmetic_sketch/),
[theorem citations](../lean/examples/sketch_in_named_theorem/),
[tuple coordinates](../lean/examples/local_tuple_sketch/) and
[finite-set membership](../lean/examples/local_finite_set_sketch/).

`eval` compiles exact scalar arithmetic: rational numbers, finite decimals,
addition, subtraction, multiplication, division, negation and closed integer
powers. It consumes the recorded numeric equality substitutions and publishes
the evaluated equality under its original FactId. Later statements can cite
that result; a result inside `sketch:` stays local. See
[exact arithmetic](../lean/examples/evaluated_arithmetic/),
[previously proved values](../lean/examples/evaluated_numeric_citations/) and
[local evaluation](../lean/examples/evaluated_local_facts/).
Numeric formula-function calls with one or two arguments also compile, including
domain guards, previously proved numeric values inside the body, nested calls
and local evaluation. The result retains each body rewrite and its exact
citations; the compiler applies the existing function beta laws before checking
the resulting arithmetic. See [formula calls](../lean/examples/evaluated_formula_calls/),
[captured values](../lean/examples/evaluated_captured_values/),
[nested calls](../lean/examples/evaluated_nested_calls/) and
[local calls](../lean/examples/evaluated_local_calls/).
Range and finite-set sums/products also compile through `eval`, using the same
denotation proofs as the aggregate calculation rule. The compiler checks the
recorded enumeration, each checked function application and every accumulated
value. This includes empty finite sets, rational terms, arithmetic combinations,
named iterands and local evaluation. For example:

```litex
eval sum(1, 3, fn(x Z) Z {x})
sum(1, 3, fn(x Z) Z {x}) = 6
```

See [range evaluation](../lean/examples/evaluated_range_aggregates/),
[finite-set evaluation](../lean/examples/evaluated_finite_aggregates/),
[combined aggregates](../lean/examples/evaluated_aggregate_arithmetic/),
[named calls](../lean/examples/evaluated_aggregate_calls/) and
[local aggregates](../lean/examples/evaluated_local_aggregates/).
`reduce` and `finite_set_reduce` evaluation also compile. Ordered folds preserve
the seed and ascending index order; finite-set folds consume the original
commutativity and associativity proofs. For example:

```litex
eval finite_set_reduce({3,1,2}, fn(k Z) Z {k}, fn(a,b Z) Z {a+b}, 10)
finite_set_reduce({3,1,2}, fn(k Z) Z {k}, fn(a,b Z) Z {a+b}, 10) = 16
```

See [ordered subtraction](../lean/examples/evaluated_range_folds/),
[finite, empty and singleton folds](../lean/examples/evaluated_finite_folds/),
[rational products](../lean/examples/evaluated_rational_fold/),
[combined expressions](../lean/examples/evaluated_fold_arithmetic/),
[named functions](../lean/examples/evaluated_named_fold/) and
[local results](../lean/examples/evaluated_local_fold/).
Exact evaluation also covers `abs`, `min`, `max`, `sign`, `floor` and `ceil`,
including negative fractions:

```litex
eval floor(-7/3)
floor(-7/3) = -3
```

The compiler consumes the original child WD, citations and ordered evaluations,
then applies existing numeric laws in `Litex.lean`. It retains cached WD objects;
when `-3` and `neg(3)` have different Lean representations, it proves their
matching denotations before composing the recorded proof.
See [real operations](../lean/examples/evaluated_real_operations/),
[variable citations](../lean/examples/evaluated_real_citations/),
[formula functions](../lean/examples/evaluated_real_functions/),
[local evaluation](../lean/examples/evaluated_local_real_operations/),
[aggregate combinations](../lean/examples/evaluated_real_aggregates/) and
[signed-number reuse](../lean/examples/evaluated_signed_representations/).
These examples require exact rational inputs after the recorded substitutions;
this does not add symbolic evaluation or approximate irrational results.

Integer evaluation covers `gcd`, `lcm`, `%`, `quot` and `factorial`, including
signed operands, cited values, formula functions and local proof scopes:

```litex
eval gcd(54,-24)
gcd(54,-24) = 6
eval quot(-7,3)
quot(-7,3) = -3
```

The original domains remain required: integer operands, a nonzero pair for
`gcd`, a nonzero divisor for `%`, a positive divisor for `quot`, and a natural
argument for `factorial`. The compiler consumes the recorded WD and citations
and applies existing Core laws. See [integer operations](../lean/examples/evaluated_integer_operations/),
[cited values](../lean/examples/evaluated_integer_citations/),
[formula functions](../lean/examples/evaluated_integer_functions/),
[local evaluation](../lean/examples/evaluated_local_integer_operations/) and
[remainders inside a sum](../lean/examples/evaluated_integer_aggregates/).

Exact square-root evaluation is also supported when the result is rational:

```litex
eval sqrt(0.36)
sqrt(0.36) = 3/5
```

The compiler preserves the recorded nonnegativity proof and derives real
membership for closed numeric arguments from their checked denotation. See
[square roots](../lean/examples/evaluated_square_roots/),
[fractions](../lean/examples/evaluated_fractional_square_roots/),
[cited values](../lean/examples/evaluated_cited_square_roots/),
[formula functions](../lean/examples/evaluated_function_square_roots/),
[local scope](../lean/examples/evaluated_local_square_roots/) and
[square roots in a sum](../lean/examples/evaluated_square_root_aggregates/).
An exact radical that evaluates to the same canonical expression also compiles
without approximation; see [sqrt(2)](../lean/examples/evaluated_exact_square_root/)
and [a radical sum](../lean/examples/evaluated_exact_radical_sum/). The compiler
checks the exact canonical result and retains the original object WD. Radical
expressions can also simplify in the checked closed linear route, for example
`eval sqrt(12)+sqrt(27)` produces `5*sqrt(3)`; see
[radical simplification](../lean/examples/evaluated_radical_simplification/)
and [a difference](../lean/examples/evaluated_radical_difference/). This route
checks the exact result and the original WD, then proves the root rewrites in
Lean. Direct products of two square roots of nonnegative rational numbers
also compile, including [sqrt(2)*sqrt(3)](../lean/examples/evaluated_radical_product/)
and [a rational result](../lean/examples/evaluated_radical_square/). These
evaluations can also replay recorded equality citations, as in
[a cited root](../lean/examples/evaluated_cited_irrational_root/) and
[a cited product](../lean/examples/evaluated_cited_radical_product/). The
rewritten intermediate is interpreted as a semantic value; the source and
result objects keep their original WD evidence. Products of two linear radical
sums also compile; see [a product of sums](../lean/examples/evaluated_radical_sum_product/)
and [a cited product](../lean/examples/evaluated_cited_radical_sum_product/).
The compiler combines repeated root pairs and limits each expansion to 64
nonzero pairs. Nested products of sums, division, function calls and aggregate
records remain outside these radical routes.
The selected rule that a positive real has a nonzero square root also replays
through the proved `Litex.sqrtNonzeroOfPositive` theorem; see
[the generic theorem](../lean/examples/square_root_nonzero_theorem/).
The selected square-root monotonicity rule replays the original argument
order and the two square-root WD proofs; see
[square-root monotonicity](../lean/examples/sqrt_monotone/).

For a positive-indexed real sequence, `lim(a)` now keeps the original sequence
domain and convergence evidence. Its semantic value is selected independently
of the WD proof, and its uniqueness is proved from Litex's epsilon-tail
definition. See [the selected value](../lean/examples/sequence_limit_selected_value/),
[real membership](../lean/examples/sequence_limit_real/) and
[existence-only WD](../lean/examples/sequence_limit_exists_object/). These
generated theorems retain the model and function-semantics parameters.
The selected uniqueness rule also cites both candidate-limit facts when the
sequence is a suitably typed parameter; see [uniqueness](../lean/examples/sequence_limit_unique/).
That example also has a handwritten [Adapter](../lean/examples/sequence_limit_unique/Adapter.lean)
and a checked [native consumer](../lean/examples/sequence_limit_unique/Final.lean).
The consumer accepts `f : ℕ → ℝ` and two Mathlib `Tendsto` hypotheses and
concludes native equality of the limits. The Adapter embeds the sequence in
the existing numeric function model, proves the conversion from `Tendsto`
to the source epsilon-tail predicate, and calls the generated uniqueness
theorem. All three Lean files pass in the pinned Lake environment; removing
the generated theorem call makes the Adapter fail. The bridge is handwritten.

Finite real function limits follow the same result-driven path. The compiler
supports `$has_limit_at`, `$has_limit_left`, `$has_limit_right` and the
proof-consuming selectors `fn_lim`, `lim_left`, `lim_right`. It keeps the
original unary function signature, real-domain evidence and candidate or
existence proof. Core proves uniqueness using both nontrivial approach through
the actual domain and the epsilon-delta condition. Examples cover
[selection](../lean/examples/function_limit_selected_value/),
[existence-only formation](../lean/examples/function_limit_exists_object/),
[equal-point citations](../lean/examples/function_limit_equal_point/),
[definition folding](../lean/examples/function_limit_definition/) and
[a guarded domain](../lean/examples/function_limit_guarded_definition/).
The [native function-limit consumer](../lean/examples/function_limit_unique/Final.lean)
uses only `ℝ → ℝ`, Mathlib punctured-neighborhood `Tendsto` hypotheses and native
equality. Its handwritten Adapter calls the generated uniqueness theorem.
A [complete punctured cancellation proof](../lean/examples/function_limit_punctured_cancellation/)
proves `x²/x → 0` from accumulation and epsilon-delta clauses. Its
[Final theorem](../lean/examples/function_limit_punctured_cancellation/Final.lean)
is the ordinary Mathlib statement
`Tendsto (fun x : ℝ => x ^ 2 / x) (𝓝[≠] 0) (𝓝 0)`.
The Adapter reads the generated estimate and the same function graph; it does
not assume convergence. Removing the generated proof makes this Adapter fail.

At positive and negative infinity, `$has_limit_pos_inf` and
`$has_limit_neg_inf` have corresponding proof-consuming selectors
`lim_pos_inf` and `lim_neg_inf`. Core retains directional unboundedness of
the actual function domain, then proves uniqueness from the epsilon/threshold
condition. Compiler examples cover
[candidate selection](../lean/examples/function_limit_pos_infinity_selected/),
[negative-direction uniqueness](../lean/examples/function_limit_neg_infinity_unique/),
[existence-only formation](../lean/examples/function_limit_pos_infinity_exists/),
[definition folding](../lean/examples/function_limit_pos_infinity_definition/)
and [guarded domains](../lean/examples/function_limit_neg_infinity_guarded_definition/).
The [constant-function example](../lean/examples/constant_function_limit_at_infinity/)
proves the two definition clauses and then uses the selected limit.
Explicit function-limit uniqueness, existence and selection calls have their own
compiler routes: `fn_limit_{at,left,right,pos_inf,neg_inf}_{unique,exists,selected}`.
Each invocation checks the reserved ID, original arguments, complete real-domain
requirements, ordered proofs and returned fact before citing the corresponding
Core theorem. See [an explicit uniqueness call](../lean/examples/function_limit_at_unique_by_theorem/)
and [an explicit existence release](../lean/examples/function_limit_at_exists_by_theorem/).
Other explicit limit laws remain outside these routes.

Exact rational logarithms also compile when Litex evaluates them:

```litex
eval log(8,4)
log(8,4) = 2/3
eval log(1/3,27)
log(1/3,27) = -3
```

The compiler checks the evaluated operands, their original WD and the positive,
nonunit base and positive argument conditions, then applies the existing
`rationalLogValue` theorem. See [logarithms](../lean/examples/evaluated_logarithms/),
[rational results](../lean/examples/evaluated_rational_logarithms/),
[arithmetic](../lean/examples/evaluated_logarithm_arithmetic/),
[formula functions](../lean/examples/evaluated_logarithm_functions/) and
[local evaluation](../lean/examples/evaluated_local_logarithms/).
The native evaluator currently rejects direct `eval log(2,a)` even when an
earlier fact gives `a = 8`; this is a source-evaluation boundary.

Exact real-valued observations of closed complex expressions also compile:
`eval re(3+4*i)`, `eval img(3+4*i)` and `eval C_abs(3+4*i)` produce
`3`, `4` and `5`. The compiler retains the original object WD and proves the
numeric observation using the complex-number bridge. See
[coordinates](../lean/examples/evaluated_complex_coordinates/),
[modulus](../lean/examples/evaluated_complex_modulus/) and
[division](../lean/examples/evaluated_complex_quotient_coordinate/).
Direct evaluation of a closed complex modulus also preserves an irrational
principal root, such as `eval C_abs(1+i)` producing `sqrt(2)`; see
[the exact modulus example](../lean/examples/evaluated_irrational_complex_modulus/).
This radical route currently requires no rewritten citations, function calls
or aggregate records. The source evaluator rejects `eval re(z)` even after
defining `z = 3+4*i`.

An arbitrary Litex integer exponent can be used with a nonzero base. The
compiler obtains an integer representative from the original membership proof
and preserves the nonzero-base evidence. The selected rule for a nonzero power
is replayed through the proved `Litex.powNonzeroOfBase` theorem. See
[integer exponents](../lean/examples/integer_exponent_well_defined/),
[nonzero powers](../lean/examples/integer_power_nonzero_theorem/) and
[a sum of logarithms of integer powers](../lean/examples/logarithms_of_integer_powers/).
The selected rule that a nonzero product has nonzero factors cites the original
product fact and the proved `Litex.productNonzeroFactors` theorem; see
[nonzero product factors](../lean/examples/nonzero_product_factors/).
For real absolute values, the selected nonzero rule similarly preserves the
original argument proof; see [absolute value nonzero](../lean/examples/absolute_value_nonzero/).
The real exponential's nonzero rule and both directions of sign nonzero also
replay their selected results; see [exponential](../lean/examples/real_exponential_nonzero/),
[sign](../lean/examples/real_sign_nonzero/) and
[sign reflection](../lean/examples/real_sign_reflects_nonzero/).
For real exponentials and logarithms on positive reals, the selected strict
and weak order rules also compile in both directions. See
[exponential monotonicity](../lean/examples/exp_strict_monotone/),
[exponential order reflection](../lean/examples/exp_strict_order_reflection/),
[logarithm monotonicity](../lean/examples/ln_weak_monotone/) and
[logarithm order reflection](../lean/examples/ln_weak_order_reflection/).
For a nonzero complex argument, the selected conjugate and modulus nonzero
rules reuse the recorded premise and original WD; see
[conjugation](../lean/examples/complex_conjugate_nonzero/) and
[complex modulus](../lean/examples/complex_modulus_nonzero/).
The selected integer least-common-multiple nonzero rule also replays both
original operand proofs; see [nonzero LCM](../lean/examples/lcm_nonzero/).
The logarithm nonzero rule replays the recorded positive/nonunit guards,
including [above-one](../lean/examples/log_nonzero_above_one/),
[below-one](../lean/examples/log_nonzero_below_one/) and
[explicit nonunit](../lean/examples/log_nonzero_positive_nonunit/) cases.
The selected nonzero-sum rule cites the recorded sum fact when proving that
one summand differs from the negation of the other; see
[nonzero sums](../lean/examples/inequality_from_nonzero_sum/).
The positive-nonunit integer-power rule preserves the selected base guard,
integer exponent membership and exponent nonzero proof; see
[arbitrary integer powers](../lean/examples/positive_nonunit_integer_power/)
and [a negative exponent](../lean/examples/nonunit_negative_integer_power/).
For defined tangent and cotangent, the selected nonzero rules cite the
original sine or cosine numerator fact; see [tangent](../lean/examples/tangent_nonzero_from_sine/)
and [cotangent](../lean/examples/cotangent_nonzero_from_cosine/).
Sine and cosine nonzero facts also transfer to negated arguments by citing
the original fact; see [sine](../lean/examples/sine_nonzero_under_negation/)
and [cosine](../lean/examples/cosine_nonzero_under_negation/).
The source rule that Euler's number is not one is proved in the semantic
bridge; see [Euler's number](../lean/examples/euler_not_one/).

The checked aggregate slice uses literal integer range bounds or enumerated
finite numeric sets and function bodies that reduce to closed scalar arithmetic.
Nested aggregates inside iterands and additional body-rewrite stages remain
unsupported. Fold bodies currently cover four operations and negation; general
function calls inside them remain outside this slice.
Matrix and algorithm evaluation, other scalar operators and
general function-returning calls also remain outside the checked `eval` slice.

Order replay also covers four weak additive shifts: a nonnegative addend
preserves a lower bound, and a nonpositive addend preserves an upper bound,
with either ordering of the addends. See [lower bounds](../lean/examples/weak_additive_lower_bounds/)
and [upper bounds](../lean/examples/weak_additive_upper_bounds/). Numeric weakening
cites an earlier bound with literal integer endpoints and preserves the required
strictness: `x < 4` or `x <= 4` can supply `x < 6`. See
[numeric lower bounds](../lean/examples/weaken_numeric_lower_bounds/) and
[numeric upper bounds](../lean/examples/weaken_numeric_upper_bounds/).
These rules combine in [finite enumeration](../lean/examples/integer_rectangle_sum_bound/)
and [a reusable theorem](../lean/examples/named_integer_rectangle_sum/).

Two inequalities can also be added: `a <= b` and `c <= d` give
`a + c <= b + d`; a strict premise in either position gives a strict sum
bound. Weak bounds support crossed addend pairs too. See
[weak sum bounds](../lean/examples/componentwise_sum_bounds/),
[mixed strict bounds](../lean/examples/mixed_strict_sum_bounds/) and
[a two-step theorem with reuse](../lean/examples/three_term_sum_bound/).
The compiler retains both original child proofs and their comparison strengths.

Subtraction preserves `a <= b` as `a-c <= b-c`, and reverses the order
when the minuend is shared: `c-b <= c-a`. Both have strict variants. See
[a shared subtrahend](../lean/examples/subtract_shared_value/) and
[a shared minuend](../lean/examples/subtract_from_shared_value/).
The [real-difference example](../lean/examples/real_difference_domains/) keeps
the shared operand in its original complex carrier and uses explicit real
membership of the differences. [Strict order chains](../lean/examples/strict_order_chains/)
replay both cited bounds, with at least one strict step. The
[three-step difference theorem](../lean/examples/ordered_difference_bound/)
combines these rules and applies the exported theorem.

Binary intersection supports construction, membership from both factors,
membership projections, and subset bounds. See
[membership in both directions](../lean/examples/intersection_membership/),
[subset bounds](../lean/examples/intersection_subset_bounds/),
[a named intersection](../lean/examples/named_intersection/) and
[nested intersections with theorem reuse](../lean/examples/intersection_reassociation/).
Its Lean representation uses existing bounded separation; no additional model
law is required. The compiler keeps the two inferred memberships' original IDs.

Set equality also covers union/intersection commutativity, associativity,
idempotence and empty-set laws, [intersection distributed over union](../lean/examples/intersection_distributes_over_union/),
and [intersection simplified by a subset premise](../lean/examples/intersection_from_subset/).
See the [intersection laws](../lean/examples/set_intersection_identities/),
[union laws](../lean/examples/set_union_identities/) and
[reversed equalities](../lean/examples/set_identity_symmetry/).
Each selected builtin calls its proved semantic law; conditional simplification
consumes the original subset proof.

`set_minus(A, B)` supports [membership and its stored consequences](../lean/examples/set_difference_membership/),
[exclusion and containment](../lean/examples/set_difference_exclusion/), and
[self/empty differences and De Morgan identities](../lean/examples/set_difference_identities/).
These compose in [nested named theorems](../lean/examples/set_difference_theorem/)
and [set-valued functions](../lean/examples/set_difference_function/).
[Union over intersection](../lean/examples/union_distributes_over_intersection/)
also accepts the recorded operand permutations and either equality direction.

[Consecutive exclusions](../lean/examples/consecutive_set_difference/) combine
two differences into exclusion of a union. Containment supports
[difference and power-set monotonicity](../lean/examples/set_containment_monotonicity/),
[union bounds](../lean/examples/union_containment_bounds/), and
[nested operators and subset chains](../lean/examples/nested_set_containment/).
[Nonmembership](../lean/examples/set_operator_nonmembership/) propagates through
intersection and union. These steps compose in the named
[union-difference bound](../lean/examples/union_difference_bound/) and
[exclusion theorem](../lean/examples/outside_union_intersection/), each followed
by a source theorem call.

Finite integer intervals support `expand:` as well:

```litex
claim:
    ? forall x range(1, 3):
        x = 1 or x = 2
    expand: x $in range(1, 3)
```

The compiler consumes the stored membership, complete ordered enumeration and
returned disjunction. `range(a, b)` excludes `b`; `closed_range(a, b)` includes
it. Their constructors carry integer endpoint evidence, and inferred bounds
retain their original FactIds. See the [source/generated pair](../lean/examples/expand_half_open_integer_range/)
and the [square-bound theorem](../lean/examples/integer_range_square_bound/),
which reuses the alternatives in `by cases`. Seven interval examples pass Lean
4.31.0, including negative values, singletons and calculated endpoints. Expansion
requires exact closed integer endpoints and 1–1,024 values; interval construction
and bound projections also accept arbitrary integer endpoints.

`by for` and `by enumerate finite_set` check independent parameters over displayed
finite sets and integer intervals:

```litex
by for:
    ? forall n range(0, 4):
        n * n <= 9
    n * n <= 9
```

Each recorded assignment supplies its own binding, assumptions and proof steps.
The compiler checks complete ordered coverage and cites each emitted conclusion.
See the [four square values](../lean/examples/integer_range_square_values/),
[nonzero division with a skipped zero case](../lean/examples/guarded_integer_range_division/)
and [a loop inside a reusable theorem](../lean/examples/named_integer_range_enumeration/).
Empty intervals, negative values, singletons and calculated endpoints are also
covered. Several parameters may share a domain or use different domains:

```litex
by for:
    ? forall x range(0, 3), y range(0, 2):
        x * x + y * y <= 5
    x * x + y * y <= 5
```

See the [rectangular square bound](../lean/examples/integer_rectangle_square_bound/),
[two nonzero guards](../lean/examples/nonzero_integer_pair_division/) and
[three parameters in mixed domains](../lean/examples/finite_triple_product/).
The last parameter varies fastest. The compiler checks the entire recorded
product, capped at 1,024 assignments, before replaying any branch. Dependent
enumeration domains remain unsupported. Existing child-statement restrictions still apply;
for example, a local `have fn` declaration remains unsupported.

`release obj def` republishes definition facts by citing their original proof
IDs. It supports `let`, arbitrary carrier/set introductions, typed equalities,
plain-existential choices and formula functions. See [values and aliases](../lean/examples/released_value_definitions/),
[a guarded reciprocal](../lean/examples/released_reciprocal_definition/),
[a chosen witness](../lean/examples/released_witness_definition/) and
[local definitions](../lean/examples/released_local_definitions/).
These pairs pass Lean; local facts retain their original scope. Qualified names
and other definition families remain unsupported; tuple-definition release is
covered below.

`finite_seq(A, n)` supports arbitrary set carriers and natural lengths, including
zero. Its exact domain is `closed_range(1, n)`. The compiler replays the original
inferred function-set membership once under its FactId; later calls cite it.
See [sequence spaces](../lean/examples/finite_sequence_spaces/),
[legal indices](../lean/examples/finite_sequence_coordinates/) and
[a first-entry function](../lean/examples/finite_sequence_first/). All three
source/generated pairs pass Lean. Infinite sequences remain a separate extension.

`release tuple def` publishes a tuple's finite-sequence membership and coordinate
facts. It supports literals, aliases, empty and singleton tuples, Cartesian
members and use inside a theorem. See [pair coordinates](../lean/examples/released_tuple_coordinates/),
[boundary lengths and mixed entries](../lean/examples/released_finite_tuples/),
[Cartesian members](../lean/examples/released_cartesian_coordinates/) and
[a local tuple theorem](../lean/examples/released_local_tuple/). These four pairs
pass Lean. The compiler uses the result's original domain, return proofs and
coordinate proofs, then emits the stored FactIds.

`release cart def` connects the product to its complete bounded definition:
`cart(R,Z) = {p finite_seq(union(R,Z),2): p(1) $in R, p(2) $in Z}`.
See [the definition and its citation](../lean/examples/released_cartesian_definition/),
[empty and single-factor products](../lean/examples/empty_and_single_cartesian_products/),
[arbitrary sets](../lean/examples/generic_cartesian_definitions/) and
[a reusable theorem](../lean/examples/local_cartesian_definition/). These pairs
pass Lean. The compiler retains exact length, factor order and every coordinate
condition. Set parameters in theorem calls consume their original sethood proofs.

Further checked pairs show [expansion of a set-valued function](../lean/examples/set_function_expansion/),
[a line member satisfying its determinant equation](../lean/examples/line_membership_condition/),
and [arithmetic with an obtained real witness](../lean/examples/obtained_real_square/).
Each includes the source and actual compiler output checked by Lean.

The latest checked pairs add [two-way quantified implications](../lean/examples/equivalence_directions/),
[verified relation registration](../lean/examples/registered_equality/), and
[real minimum and maximum](../lean/examples/real_min_max/). They cover local
equivalence facts, predicates on arbitrary set objects, all three registration
declarations, min/max symmetry and idempotence, and real/integer membership.
Further pairs cover [exact min/max evaluation](../lean/examples/min_max_evaluation/)
and [operand bounds and monotonicity](../lean/examples/min_max_bounds/). The latter
retains both input comparisons, including the case where one operand stays
fixed. [Conditional selection](../lean/examples/ordered_min_max_selection/)
consumes the recorded order premise for either operand and equality orientation.
[Lower/upper functions](../lean/examples/ordered_min_max_functions/) combine
formula bodies, call unfolding, a concrete predicate, conditional named theorems,
aliases and theorem calls. Registered transitive-chain inference remains separate work.

[Real sign](../lean/examples/real_sign/) adds exact values, integer membership
and positive/negative conditional equalities. The
[shifted direction function](../lean/examples/shifted_sign_function/) uses sign
inside a formula body and a nested function call. Its denotation is bridged to
Mathlib's `Real.sign`. [Products](../lean/examples/sign_product/) and
[negation](../lean/examples/sign_negation/) now replay their selected identities,
including reversed equalities and the producer's supported negation spellings.
[Magnitude reconstruction](../lean/examples/signed_magnitude/) proves
`sign(x) * abs(x) = x` and `abs(x) = sign(x) * x` for arbitrary real members.
The [direction and magnitude functions](../lean/examples/direction_magnitude_functions/)
reuse these laws in a named theorem and in a product of function calls.

[Floor and ceiling](../lean/examples/rounding_integers/) preserve integer values
and compute exact fractions, including `floor(-3 / 2) = -2` and
`ceil(-3 / 2) = -1`. Their [bounds and monotonicity](../lean/examples/rounding_bounds/)
use proved bridges to `Int.floor` and `Int.ceil` with the original real-domain
and order evidence. [Rounding functions](../lean/examples/shifted_rounding_function/)
combine `have fn`, nested calls, a parameterized `thm` and `by thm`.

[Integer quotient and remainder](../lean/examples/signed_integer_division/)
include negative dividends and nonzero negative moduli. Quotient divisors
retain their positive-natural domain. The [decomposition example](../lean/examples/quotient_remainder_decomposition/)
proves `a = d * quot(a, d) + a % d` and the remainder bounds for arbitrary
`a ∈ Z`, `d ∈ N+`. [Division functions](../lean/examples/integer_division_functions/)
show explicit function expansion, argument equality transport and named theorem
reuse. `have d N+` and function parameters preserve the original sign and
nonzero inference IDs, which subsequent WD can cite.

[Gcd/lcm](../lean/examples/gcd_lcm_values/) now preserve signed integer inputs,
`gcd`'s nonzero-pair condition, and the distinct `N+`/`N` codomains. The
[identity examples](../lean/examples/gcd_lcm_identities/) include commutativity,
absolute values and the product law; the [Euclidean step](../lean/examples/gcd_euclidean_step/)
reuses the checked remainder construction. Their proved bridges use `Int.gcd`
and `Int.lcm`. The [function example](../lean/examples/gcd_lcm_functions/)
combines guarded `have fn`, a named `thm`, `by thm` and argument-equality reuse.
Each pair has passed actual Lean checking.

[Factorial](../lean/examples/factorial_values/) keeps its natural argument proof
and positive-natural range. [Recurrences](../lean/examples/factorial_identities/)
and [order rules](../lean/examples/factorial_order/) use proved `Nat.factorial`
bridges; strict monotonicity keeps the positive smaller-argument condition.
The [permutation-count function](../lean/examples/factorial_function/) retains
those domains in its declaration and call.

The source literal `i` uses `Complex.I` in the existing number wrapper.
[Exact calculations and aliases](../lean/examples/imaginary_unit_values/) check
both complex coordinates. [Symbolic polynomial identities](../lean/examples/complex_polynomial_identity/)
consume the selected Complex result with fixed coordinate normalization.
The [quarter-turn example](../lean/examples/complex_rotation/) defines
`rotate(z) = i * z` and uses a named theorem to prove that two calls give `-z`.
These generated pairs pass Lean.

[Signed and nonzero numeric sets](../lean/examples/signed_numeric_values/)
now include `Q+`, `Q-`, `Z-`, `R-`, `Q*`, `Z*`, `R*` and `C*`.
[`have` declarations](../lean/examples/signed_numeric_declarations/) and
[arbitrary parameters](../lean/examples/signed_numeric_domains/) publish the
original sign/nonzero FactIds for later WD. [Conditional refinement](../lean/examples/refined_numeric_membership/)
consumes the recorded base membership and guard. [Functions](../lean/examples/signed_numeric_functions/)
retain these domains and codomains on the existing Litex call object.
The sets are bounded separations in `SetSemantics`; no model fields or axioms
are added. [Direct subset statements](../lean/examples/signed_numeric_subsets/)
replay the selected standard-inclusion rule.

[Positive and nonzero products/quotients](../lean/examples/refined_products/)
retain their refined membership through the original operand proofs and WD.
The [rational reciprocal](../lean/examples/nonzero_rational_reciprocal/),
[positive scaling functions](../lean/examples/positive_scaling_functions/) and
[reciprocal-product theorem](../lean/examples/nonzero_rational_product_theorem/)
combine these codomains with nested calls and named theorem reuse.
[Numeric nonmembership](../lean/examples/numeric_nonmembership/) includes
`not 1 / 3 $in Z` and `not i $in R`;
[finite nonmembership](../lean/examples/finite_nonmembership/) includes
`not 4 $in {1, 2, 3}` and disequality from membership in the same set.
All six generated pairs pass Lean.

[Negated universals](../lean/examples/not_every_element_is_one/) now replay
counterexample existence proofs. The [reciprocal example](../lean/examples/reciprocal_counterexample/)
keeps the nonzero guard; [multiple conclusions](../lean/examples/incompatible_universal_equalities/)
and [alternatives](../lean/examples/alternatives_counterexample/) use the recorded
De Morgan transformation. [Real counterexamples](../lean/examples/real_counterexamples/)
include arbitrary free objects, multiple bound variables, order and a local
theorem. The inference's existence fact has its own original `h_<fact_id>`.
Negated premises and contradiction goals also consume their retained formation
evidence; examples appear below.

[Negative existence](../lean/examples/no_one_in_zero_singleton/) now compiles
through a recorded contradiction proof and exact later fact citations. The
[reciprocal example](../lean/examples/nonzero_reciprocal_reflexivity/) obtains
a witness with its real membership and nonzero guard before using division.
[A reusable theorem](../lean/examples/incompatible_existential_equalities/)
also exercises `claim` and `by thm`; [an alternative body](../lean/examples/no_self_unequal_alternative/)
keeps the runtime's decision not to produce a De Morgan inference. All four
source/generated pairs pass strict source verification, identical regeneration
and Lean 4.31.0; generated files are 2,162–14,099 bytes. The compiler emits any
recorded De Morgan forall under its original FactId, deriving it from the
negative existential. This increment adds no semantic-model fields or axioms.
Automatic applications of a universal negative-existence theorem are covered below.

[Unique existence](../lean/examples/unique_real_zero/) now consumes both the
witness and its recorded uniqueness proof. The generated meaning is existence
conjoined with pairwise `Litex.Same` uniqueness. [Two coordinates](../lean/examples/unique_real_pair/)
use the original tuple equality and derive the stored componentwise equalities.
[A reciprocal value](../lean/examples/unique_reciprocal_value/) retains the
free object's host representation and nonzero-domain evidence.
[A saved theorem and claim](../lean/examples/unique_real_theorem/) and
[a universally quantified theorem call](../lean/examples/unique_copy_theorem/)
exercise reuse and `obtain`. All five pairs pass strict source verification,
identical regeneration and Lean 4.31.0; generated files are 11,601–30,010 bytes.
All 45 exported declarations use only standard axioms. No Core or semantic-model
fields were added. The bijective-preimage builtin remains unsupported;
unique-existence function declarations are covered below.

Automatic theorem lookup now replays universal conclusions in all three
existential families. Four pairs cover [a unique copy](../lean/examples/automatic_unique_copy/),
[a nonzero reciprocal](../lean/examples/automatic_unique_reciprocal/),
[a pair of coordinates](../lean/examples/automatic_unique_pair/), and
[an excluded copy](../lean/examples/automatic_excluded_copy/). The coordinate
example also uses unique existence as ordinary existence, both through a saved
fact and through a universal theorem. The compiler checks the original citation,
conclusion position, parameter substitution, argument-match evidence and domain
proofs. It retains Runtime's requirement that the instantiated existential body
matches the goal up to bound-name renaming. All four pairs pass strict source
verification, identical regeneration and Lean 4.31.0; their generated files are
6,206–24,063 bytes. This increment changes compiler consumers only.

Functions can now be selected from a proved unique-output specification using
`have fn … by exist!`. Four source/generated pairs cover
[identity](../lean/examples/selected_identity_function/),
[a guarded reciprocal](../lean/examples/selected_reciprocal_function/),
[two-input addition](../lean/examples/selected_sum_function/), and
[identity on an arbitrary set](../lean/examples/selected_set_identity_function/).
The last example does not assume the set is inhabited. Calls cite the stored
property, including the final calculation `selected(2, 3) = 5`.
All four pass strict Litex and Lean 4.31.0; generated files are
12,928–28,112 bytes. The declaration currently requires one output witness,
uses the existing supported function domains, and is restricted to top level.

`by contra` now accepts `forall` and `not forall` goals with the supported
quantifier-free bodies, including [nonzero reciprocal guards](../lean/examples/contradiction_with_reciprocal_guard/).
A [negated universal premise](../lean/examples/negated_universal_premise/) can
also supply a counterexample to `obtain` inside a named theorem. The compiler
replays the original WD and assumption stores, keeping their FactIds and local
visibility. Four new pairs pass actual Lean checks; generated files are
2,407–7,953 bytes. These cases use atomic contradiction closings.

Unique-existence goals also compile through `by contra`. Examples cover
[two coordinates](../lean/examples/unique_pair_by_contradiction/),
[a guarded reciprocal](../lean/examples/unique_guarded_value_by_contradiction/),
[a reusable theorem](../lean/examples/unique_copy_by_contradiction/),
[set objects](../lean/examples/unique_set_copy_by_contradiction/) and
[a dependent carrier](../lean/examples/unique_dependent_pair_by_contradiction/).
The compiler preserves the recorded alternative-witness assumption and proves
uniqueness using equality of denotations. All six pairs pass actual Lean.

Contradictions can also close with a complete quantified formula:
[`impossible forall …`](../lean/examples/universal_contradiction_closing/),
[a nonzero guard](../lean/examples/guarded_universal_contradiction_closing/),
[`impossible not forall …`](../lean/examples/counterexample_contradiction_closing/),
and [`impossible exist! …`](../lean/examples/unique_contradiction_closing/),
including [two unique coordinates](../lean/examples/unique_pair_contradiction_closing/).
Both original closing proofs are replayed before applying their logical contradiction.
A [named counterexample theorem](../lean/examples/named_counterexample/) can be
invoked and its inferred existence fact consumed by `obtain`.

A local universal assumption is stored over `M.Value`. Each citation converts
its supplied objects to semantic representatives, preserving membership/domain
FactIds and leaving the source objects' representations unchanged. This lets
[one assumption be used at a numeral and then at a semantic witness](../lean/examples/counterexample_after_universal_use/)
without fixing its callers to one Lean universe. These seven new pairs and nine
neighboring pairs pass strict Litex, identical regeneration and Lean 4.31.0;
43 exported declarations use only the standard axioms. The new generated files
are 3,712–23,575 bytes. Runtime, result types and `Litex.lean` are unchanged.

`have fn … by cases` also compiles: examples cover
[absolute value](../lean/examples/piecewise_absolute_value/),
[a reciprocal extended to zero](../lean/examples/piecewise_total_reciprocal/),
[two-input maximum](../lean/examples/piecewise_larger_value/) and
[a reciprocal magnitude with a nonzero domain](../lean/examples/piecewise_inverse_magnitude/).
The declaration consumes the original coverage, disjointness and return-WD
checks. A call retains the selected guard proof and cites the stored branch
equation. All four generated files pass Lean 4.31.0 and are about 14–35 KB.
This checked slice covers top-level declarations with one or two real inputs
and two branches; the reciprocal example also proves its equation for an
arbitrary nonzero input. `Litex.lean` derives the piecewise graph and call law
from existing function semantics, without new model assumptions.

Mapping properties now replay their original definition proofs and inferred
facts: `$injective(A, B, f)`, `$surjective(A, B, f)` and `$bijective(A, B, f)`.
Examples prove the [real identity is bijective](../lean/examples/identity_bijection/),
[use mapping properties as premises](../lean/examples/mapping_property_inference/),
and [prove translation by one is bijective](../lean/examples/shift_bijection/).
The [unique-preimage example](../lean/examples/bijective_unique_preimages/) works
with arbitrary sets and a unary function, in either equation orientation.
Its selected builtin consumes the stored bijection certificate and target
membership; inferred facts keep their original FactIds. `Litex.lean` defines
these properties over semantic values and proves the bridges from existing
function laws, with no new model fields or axioms. The four generated files
pass Lean 4.31.0, occupy 13–27 KB and export 28 audited theorems.
This slice checks exact unary callable signatures; carrier-equality and
finite-prefix WD alternatives remain separate compiler work.

Function ranges and preimage declarations now compile too:

```litex
have fn shift(x R) R = x + 1
shift(2) $in fn_range(shift)
have by fn_preimage: a from shift(2) $in fn_range(shift)
a $in R
shift(a) = shift(2)
```

See the paired [shift example](../lean/examples/shift_range_preimage/),
[nonzero reciprocal preimages](../lean/examples/reciprocal_range_preimage/),
[two-input preimages](../lean/examples/sum_range_preimage/) and
[range members on arbitrary sets](../lean/examples/function_range_members/).
These include a preimage declaration inside a named theorem. Each passes strict
Litex, identical regeneration and Lean 4.31.0; the files occupy 9–55 KB.

`fn_range(f)` denotes the range of the semantic graph, independently of which
function signature supplies its WD. `Litex.lean` derives this set and its
membership/preimage laws from existing separation and function-graph laws.
The source producers now retain the signature and exact property FactId they
already selected, plus the actual preimage parameter list. The compiler uses
these and the ordered returned membership/guard/equality stores; it does not
search for a new signature. A preimage declaration supplies its call constructor
from those stores, and its existence proof is emitted once and then cited.
Runtime storage, proof search and the source AST are unchanged.

The range builtin also accepts [anonymous function calls](../lean/examples/anonymous_function_ranges/),
including a two-input quotient with a nonzero guard. It consumes the original
function-equality certificate and call WD. Renaming a literal's bound parameters
is checked as alpha-equivalence before the corresponding Lean reflexivity proof.

Preimages now retain [positive-real membership](../lean/examples/positive_range_preimage/),
including [two positive coordinates](../lean/examples/positive_pair_preimage/) and
[positive inputs with two explicit conditions](../lean/examples/guarded_positive_preimage/).
The latter also obtains a preimage inside a named theorem. The compiler splits
the signature's ordered positivity and explicit guards, restores each `R+`
membership, then exports the original condition FactIds. These four additional
pairs pass strict Litex, identical regeneration and Lean 4.31.0; their generated
files occupy 15–95 KB. Core semantics and result producers are unchanged.

The set objects `preimage(f, y)` and `preimage_set(f, Y)` also compile. They
contain the legal inputs whose output equals `y` or belongs to `Y`, retaining
all input carriers and guards. Membership supplies those original conditions
and the output fact under their recorded FactIds; containment in the original
input carrier is supported. Multiple inputs are packed into a Cartesian tuple.
See [guarded reciprocal fibers](../lean/examples/guarded_reciprocal_preimages/),
[two-input quotient fibers](../lean/examples/binary_quotient_preimages/),
[abstract functions](../lean/examples/abstract_function_preimages/) and
[positive input domains](../lean/examples/positive_domain_preimages/).
All four pairs pass strict Litex, identical regeneration and Lean 4.31.0.
Their generated files occupy 18–81 KB. The Core laws follow from existing
separation and function-graph semantics; this increment changes no Runtime,
AST or result producers.

The function object `compose(f, g)` / `f ∘ g` retains `g`'s complete domain
and checks that its output satisfies `f`'s input conditions. Replay covers
construction, complete function membership, calls, output membership and the
recorded beta steps. See [squared differences](../lean/examples/squared_gap_composition/),
[shifted squares](../lean/examples/shifted_square_composition/),
[double reciprocal](../lean/examples/double_reciprocal_composition/),
[abstract functions](../lean/examples/abstract_function_composition/) and
[positive input domains](../lean/examples/positive_domain_composition/).
All five source/generated pairs pass strict Litex and Lean 4.31.0. The
[graph-law pair](../lean/examples/composition_graph_laws/) additionally checks
associativity, identity, equality to the defining lambda (including a wider
verified return carrier), and containment in the outer function's range.
[Guarded identities](../lean/examples/guarded_composition_identities/) retain
the nonzero input condition; [abstract associativity](../lean/examples/abstract_composition_associativity/)
uses arbitrary real-function parameters. These three pairs also pass actual
Lean checks. Complete-domain matching also consumes the recorded forward and
reverse inclusion proofs. They establish domain equality by set extensionality;
the compiler keeps their exact FactIds and local scope. This supports both right
identity and `by fn_extension` with differently written domains. See
[positive shifts](../lean/examples/equal_positive_shifts/) and
[reordered domain conditions](../lean/examples/reordered_function_domains/).
`by fn_extension` also accepts two inputs and `R+` inputs: see
[binary sums](../lean/examples/equal_binary_sums/) and
[guarded quotient formulas](../lean/examples/equal_guarded_quotients/).
It still rejects more than two inputs. Composition construction retains its
separate restriction on changing the packed-domain representation.

`release thm fn_set_member(...)` and selected `by thm fn_set_member(...)`
also consume the recorded domain inclusions before the original return proofs.
They cover [reordered guards](../lean/examples/reordered_function_membership/),
[`R+` versus an explicit positive-real domain](../lean/examples/positive_function_membership/),
[cited arbitrary functions](../lean/examples/abstract_function_membership_domains/),
and [composition as the function source](../lean/examples/composed_quotient_membership/).
Domain equality preserves the whole graph; it does not restrict an existing
function to fewer inputs.


A function parameter can return another function. Each application consumes its
own captured argument and guard proofs:

```litex
forall provider fn(t R: t != 0) fn(x, y R: y != 0) R:
    provider(2)(3, 4) $in R
```

The [generated calls](../lean/examples/returned_function_values/) include two and
three layers. Their returned functions also support [range construction](../lean/examples/returned_function_ranges/),
[preimage construction](../lean/examples/returned_function_preimages/) and
[a named theorem widening real outputs to complex outputs](../lean/examples/returned_function_membership/).
The shared consumer reads `ApplicationReturn` directly, including its local WD
IDs; `FunctionSemantics.call_mem` proves membership from the recorded domain.
These four pairs pass strict Litex execution and Lean 4.31.0. Return signatures
are fixed; complete-domain recovery after several call layers remains pending.

Definitions can construct a returned function or take a function as input:

```litex
have fn selected_shift(t R) fn(x R) R = fn(x R) R {x + 1}
have fn keep_function(f fn(x R) R) fn(y R) R = f
forall f fn(x R) R:
    keep_function(f) = f
```

The [returned shift](../lean/examples/selected_shift_function/) also names the
result, records its signature and proves `chosen_shift(2) = 3`. The
[identity operator](../lean/examples/function_identity_operator/) checks the
function-valued input and output. [Anonymous function membership](../lean/examples/literal_function_signatures/)
preserves unary and binary nonzero guards while allowing binder renaming.
All three pairs pass strict Litex execution and Lean 4.31.0; they reuse the
existing function semantics and original constructor WD.

Returned numeric functions can also capture an enclosing parameter:

```litex
have fn shifted_by(t R) fn(x R) R = fn(x R) R {x + t}
forall t R:
    shifted_by(t) = fn(x R) R {x + t}
    shifted_by(t)(2) = 2 + t
```

The [shift example](../lean/examples/captured_shift_functions/) also checks
positive-real membership. Further pairs cover [outer and inner nonzero guards](../lean/examples/captured_division_functions/),
[two inner parameters](../lean/examples/captured_binary_functions/) and
[immediate application of a captured function](../lean/examples/nested_function_application/).
All four pass strict Litex and Lean 4.31.0. The compiler retains the original
WD proofs and parameter IDs; it replays the recorded beta steps and later
argument groups. Dependent carrier sets and other complete-domain evidence
variants remain outside these checks.

Coverage refers to implemented and checked constructions and proof routes;
it does not mean every Litex proof in this mathematical area can be compiled.
Absolute value, symbolic natural powers and selected disjunctions also have
bounded replay and local Lean checks. The recursive Newton estimate has a
checked generated Lean proof; its native all-index interface remains unfinished.
See the [Newton example status](examples/litex_to_lean/newton_residual/README.md#recursive-residual-bound).

Start with the [complete add-zero and Adapter example](examples/litex_to_lean/add_zero/README.md),
then follow the [rational inverse-map walkthrough](#two-rational-maps-from-definitions-to-a-native-equivalence).
Each example directory in the table contains its `.lit` source beside the
actual generated `.lean`. Browse the [full source/generated collection](../lean/examples/)
to see how these capabilities combine into proofs that Lean can consume.

The [coverage plan](Litex_To_Lean_Coverage_Plan.md) inventories the remaining
statement, object and builtin-rule routes as of 2026-10-23 and groups them into
implementation phases. Its counts describe compiler entrypoints and planned
work; the examples above provide the checked mathematical coverage.
