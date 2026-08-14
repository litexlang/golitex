# Universal `Litex.Object` design

Last reviewed: 2026-08-13

This is the consolidated design ledger for the Litex-to-Lean object ABI. It
records the decisions that new compiler work must follow, the exact boundary
between Litex verification and Lean replay, and ten representative examples.

The design and the current implementation are not yet identical. In this
document:

- **Current** means the universal-object emitter produces and tests this shape
  today.
- **Decided** means the design has been accepted and is normative, but some
  compiler work is still required.
- **Open spelling** means the semantic obligation is fixed while the final Lean
  declaration name or packaging has not been frozen.

The shared ABI and builtin proofs live in
[`lean/Litex/Core.lean`](../../lean/Litex/Core.lean) and
[`lean/Litex/BuiltinRules.lean`](../../lean/Litex/BuiltinRules.lean). The exact
import plus ABI-version check emitted today is checked in as
[`current_generated_file_header.lean`](current_generated_file_header.lean), and
Rust tests require the compiler, shared core, and checked-in header to agree.

## 1. One universe of objects

Every Litex object lowers to one Lean type:

```lean
namespace Litex

axiom Object : Type

end Litex
```

This includes:

- ordinary values;
- user-defined sets;
- `N`, `Z`, `Q`, `R`, `C`, and their refined subsets;
- function-space objects such as `fn(x R) R`;
- function values;
- objects produced by function calls;
- list sets, replacement sets, and other set constructors.

There is no `Litex.Object α`, carrier inference, native binder such as
`x : ℝ`, widening, downcast, or conversion between memberships. Lean equality
on `Litex.Object` is Litex object equality.

### Why this is source semantics, not target-side type erasure

The universal carrier follows Litex itself. The runtime represents numbers,
functions, standard numeric sets, function spaces, and set constructors in the
same [`Obj`](../obj/obj.rs) syntax tree. Its builtin rule for
[`$is_set(x)`](../verify/verify_builtin_rules/non_equational_dispatch.rs)
accepts every well-defined object with the explanation "Every object is a
set." Set operations consequently check that their operands are well-defined
objects, while set builders remain bounded by an existing ambient object; see
the [set-constructor WD rules](../verify/verify_obj_well_defined/sets.rs).

This is the pure-set specialization of the working foundation used in Tao's
*Analysis I*. Definition 3.1.1 and Axiom 3.1 first treat sets as objects, while
Remark 3.1.3 explicitly leaves the choice between pure and impure set theories
open. Litex chooses the pure branch: numbers and functions retain their
ordinary public interfaces, but at the foundational level they are set-coded
objects. The compiler-facing consequence is exercised by the tracked
[universal-object tracer](../../examples/05_compiler_interop/compile_to_lean_litex_object_abi.lit).

`Object : Type` is the Lean meta-level carrier of this object language; it is
not itself a term of type `Object`. The declaration therefore does not create
an internal universal set, does not assert `Object ∈ Object`, and does not claim
to contain every Lean type or function. It says only that every source-level
Litex object has one target representation.

This ontology does not by itself establish a full model of ZF or ZFC. The
semantic core still needs an auditable model or relative-consistency argument
as its set-constructor laws grow. The compiler claim is narrower: its target
ABI must faithfully replay the object, membership, extensionality, and
well-definedness judgments that Litex actually accepted.

## 2. Every object is a set; membership is independent

The decided set foundation is:

```lean
namespace Litex

axiom In : Object → Object → Prop

def IsSet (_ : Object) : Prop := True

def IsNonemptySet (s : Object) : Prop :=
  ∃ x : Object, In x s

def IsFiniteSet (s : Object) : Prop :=
  Set.Finite {x : Object | In x s}

end Litex
```

`Litex.In x S` is a proposition about two objects. It never changes the Lean
type of `x`. The same object may simultaneously belong to `C`, `R`, a
user-defined set, and any number of function spaces.

Source binders still retain their exact source facts even when the fact is
definitionally easy. For example, `forall S set` may still emit a parameter
proof `Litex.IsSet S`; the compiler must not erase a verifier-owned `FactId`
merely because Lean can prove the proposition with `True.intro`.

Because every object is a set, equality is extensional in the decided model:

```lean
axiom Litex.ext {A B : Litex.Object} :
  (∀ x : Litex.Object, Litex.In x A ↔ Litex.In x B) → A = B
```

This does not license unrestricted comprehension. There must be no constructor
of the form

```lean
-- forbidden
setOf : (Litex.Object → Prop) → Litex.Object
```

with an unrestricted membership equivalence. Source set builders must use a
restricted source contract, and partial constructors must carry their Litex
well-definedness certificate.

### Implemented pure-set boundary

The shared `Litex.Core` module now contains:

```lean
namespace Litex

def IsSet (_ : Object) : Prop := True

end Litex
```

and derives nonemptiness and finiteness directly from the membership extension.
Source `$is_set` proofs still retain their own `FactId`; definitional truth is
not used as a reason to erase verifier evidence.

## 3. Standard numeric sets and one numeral object

Every standard numeric domain is a `Litex.Object`:

```lean
axiom Litex.N : Litex.Object
axiom Litex.Z : Litex.Object
axiom Litex.Q : Litex.Object
axiom Litex.R : Litex.Object
axiom Litex.C : Litex.Object
```

Refined domains such as `N+`, `Z*`, `R+`, and `R*` are additional set objects,
not Lean subtypes. They are emitted in the common file header whether or not a
particular source file mentions them.

An Arabic numeral denotes one object. The current bridge embeds Mathlib
complex numbers:

```lean
axiom Litex.embedComplex : ℂ → Litex.Object

instance (n : Nat) : OfNat Litex.Object n where
  ofNat := Litex.embedComplex (n : ℂ)
```

Separate theorems establish memberships such as `1 ∈ N`, `1 ∈ R`, and
`1 ∈ C`. Those theorems do not create three different objects.

Litex does not overload source `+`. Every source occurrence denotes the one
Litex complex addition operation. Real or integer closure is justified by
ordinary builtin-rule theorems using retained membership proofs. ABI version 7
makes addition, subtraction, multiplication, and division proof-carrying:

```lean
axiom Litex.add (a b : Litex.Object) :
  Litex.In a Litex.C → Litex.In b Litex.C → Litex.Object
```

`Litex.sub` and `Litex.mul` have the same ordered contract. `Litex.div` has the
additional exact denominator-nonzero slot:

```lean
axiom Litex.div (a b : Litex.Object) :
  Litex.In a Litex.C → Litex.In b Litex.C → b ≠ 0 → Litex.Object
```

## 4. Function spaces are set objects

One source function layer is described by a restricted specification:

```lean
structure Litex.FnSpec where
  arity : Nat
  requirements : List Litex.Object → Prop
  range : List Litex.Object → Litex.Object

axiom Litex.FnSet : Litex.FnSpec → Litex.Object
```

For example, `fn(x R : x > 0) R` is one `FnSet` object whose requirement for
`[x]` contains both `Litex.In x Litex.R` and the translated `x > 0` fact. A
function value is not assigned a native Lean function type. Its contract is a
membership fact:

```lean
hf : Litex.In f (Litex.FnSet spec)
```

If Litex later records `f` in another function space, the old membership fact
does not become false or change `f`. Each source call cites the exact function-
space membership `FactId` selected by the verifier. A runtime convenience slot
may select the latest callable contract, but it must not destroy older facts
that are explicitly citable.

## 5. Calls preserve exact Litex application layers

Application is proof-carrying:

```lean
axiom Litex.Applicable :
  Litex.Object → List Litex.Object → Prop

axiom Litex.apply :
  (f : Litex.Object) →
  (args : List Litex.Object) →
  Litex.Applicable f args →
  Litex.Object
```

Generated Lean uses direct list syntax through the current `CoeFun` instance;
there is no surface macro:

```text
f(a, b) -> f [a, b] well_defined_fact
f(a)(b) -> (f [a] first_well_defined_fact) [b] second_well_defined_fact
```

Application groups are exact:

- `f(1, 2, 3)` is one layer containing three arguments.
- `g(1)(2)` is two layers.
- Lean currying must never turn a Litex-rejected grouping into a valid call.
- Every layer receives its own `Applicable` proof.

Membership in a function space builds applicability and proves the result
membership:

```lean
axiom Litex.fnSetApplicable
    {f : Litex.Object} {spec : Litex.FnSpec}
    {args : List Litex.Object} :
  Litex.In f (Litex.FnSet spec) →
  args.length = spec.arity →
  spec.requirements args →
  Litex.Applicable f args

axiom Litex.fnSetResult
    {f : Litex.Object} {spec : Litex.FnSpec}
    {args : List Litex.Object}
    (hf : Litex.In f (Litex.FnSet spec))
    (hLength : args.length = spec.arity)
    (hRequirements : spec.requirements args) :
  Litex.In
    (Litex.apply f args
      (Litex.fnSetApplicable hf hLength hRequirements))
    (spec.range args)
```

If the range is another `FnSet`, `fnSetResult` supplies the membership needed
for the next source application layer.

## 6. WD evidence is part of partial object construction

The decided rule is:

> If Litex needs a nontrivial WD proof before an object expression exists,
> the corresponding Lean object constructor or call consumes that proof.

The proof is not merely a detached audit comment. Examples include:

- function application and every later application layer;
- anonymous-function construction and its range obligation;
- list-set construction when Litex requires pairwise-distinct entries;
- replacement construction when Litex requires output uniqueness;
- partial user-defined and builtin operations.

Constructor-specific propositions make the boundary explicit:

```lean
def Litex.ListSetWellDefined (xs : List Litex.Object) : Prop :=
  xs.Pairwise (· ≠ ·)

axiom Litex.listSet :
  (xs : List Litex.Object) →
  Litex.ListSetWellDefined xs →
  Litex.Object

def Litex.ReplacementWellDefined
    (P : Litex.Object → Litex.Object → Prop)
    (A : Litex.Object) : Prop :=
  ∀ x, Litex.In x A →
    ∀ y₁ y₂, P x y₁ → P x y₂ → y₁ = y₂

axiom Litex.replacement :
  (P : Litex.Object → Litex.Object → Prop) →
  (A : Litex.Object) →
  Litex.ReplacementWellDefined P A →
  Litex.Object
```

`ListSetWellDefined`, `listSet`, and `inListSet_iff` are implemented in ABI
version 5. The replacement declarations remain a decided semantic shape whose
exact target spelling is not implemented yet.

All certificates inhabit `Prop`. Lean proof irrelevance therefore prevents
the chosen proof route from becoming mathematical data. For example, two
proofs `h₁ h₂ : ListSetWellDefined xs` are equal, so the two applications of
`listSet xs` can be proved equal. The compiler still records which proof route
Litex actually used.

## 7. Anonymous functions carry construction WD

An anonymous function is a function object, not a native Lean lambda exported
as the source value. Its target construction must retain at least:

1. its `FnSpec`;
2. a body available under the exact ordered argument requirements;
3. the WD proof DAG for the body;
4. a proof that every legal body result belongs to the declared range.

The exact Lean packaging is **open spelling**, but the required shape is
equivalent to:

```lean
def Litex.AnonymousFnWellDefined
    (spec : Litex.FnSpec)
    (body : List Litex.Object → Litex.Object) : Prop :=
  ∀ args,
    args.length = spec.arity →
    spec.requirements args →
    Litex.In (body args) (spec.range args)

axiom Litex.anonymousFn :
  (spec : Litex.FnSpec) →
  (body : List Litex.Object → Litex.Object) →
  Litex.AnonymousFnWellDefined spec body →
  Litex.Object
```

If constructing `body args` itself needs the requirement proof, the final Lean
field must take that proof as an argument. The compiler may not totalize an
undefined source body merely to fit the simpler sketch above.

## 8. Set constructors and semantic laws

Total primitive set operations may be ordinary object constructors:

```lean
axiom Litex.empty : Litex.Object
axiom Litex.union : Litex.Object → Litex.Object → Litex.Object
axiom Litex.intersect : Litex.Object → Litex.Object → Litex.Object
axiom Litex.setMinus : Litex.Object → Litex.Object → Litex.Object
axiom Litex.powerSet : Litex.Object → Litex.Object
```

Their membership meanings belong to the small semantic core:

```lean
axiom Litex.inEmpty_iff {x : Litex.Object} :
  ¬ Litex.In x Litex.empty

axiom Litex.inUnion_iff {x A B : Litex.Object} :
  Litex.In x (Litex.union A B) ↔ Litex.In x A ∨ Litex.In x B

axiom Litex.inIntersect_iff {x A B : Litex.Object} :
  Litex.In x (Litex.intersect A B) ↔
    Litex.In x A ∧ Litex.In x B
```

Concrete Litex builtin rules such as union commutativity are then real Lean
theorems derived from these semantic laws and `Litex.ext`. They must not be
added as independent axioms.

Partial constructors such as `listSet` and `replacement` additionally take
their WD proof as described above. The membership theorem refers to the
proof-carrying object:

```lean
axiom Litex.inListSet_iff
    {x : Litex.Object} {xs : List Litex.Object}
    {h : Litex.ListSetWellDefined xs} :
  Litex.In x (Litex.listSet xs h) ↔ x ∈ xs
```

## 9. Verifier-owned object identities and replay order

The Lean emitter does not re-run Litex verification or search for an equivalent
target proof. The verifier freezes:

- `SourceObjectOccurrenceId` for each source occurrence;
- `FactId` for every environment-stored fact;
- `WellDefinedObjId` for each fixed object created after a successful WD check;
- `WellDefinedFactId` for each factual obligation used by that DAG;
- direct child edges, target requirement roles, source scope, root execution
  phase, and the exact function-space membership contract.

Lean declarations use stable names such as:

```lean
theorem well_defined_fact_17 ... :
    Litex.In (Litex.add a b a_in_C b_in_C) Litex.C := by
  exact Litex.BuiltinRules.complexAddClosure a_in_C b_in_C
```

Children are emitted before parents. If the proof is needed in another
theorem's type, its helper is emitted before that theorem and generalized over
the visible Litex environment. An outer term then passes
`well_defined_fact_17` to its proof-carrying constructor. A WD cache hit cites
the original accessible ID; it does not become a proofless boolean. Root uses
retain preflight/proof/store phase so equal source objects do not force a
structural guess. Child environments see parent facts, discarded child facts
do not leak, and committed scopes follow the runtime's real merge rules.

`WellDefinedObjId` is deliberately not named `WellDefinedObjProofId`. The
identity denotes the fixed object that becomes available after WD succeeds;
its construction happens to be justified by a proof DAG. Runtime cache
entries, frozen statement certificates, To-Lean IR, and Lean emission all use
that same identity. The stable target spelling is:

```text
WellDefinedObjId(12)  -> obj_12
WellDefinedFactId(17) -> well_defined_fact_17
```

When Lean's proof-carrying application ABI needs a target-only
`Litex.Applicable` bridge, its stable helper name is derived from the object
identity rather than consuming a second verifier fact identity:

```text
WellDefinedObjId(12) -> obj_12_applicable
```

If that application is a callable prefix, its checked return membership is
also exposed under the same identity:

```text
WellDefinedObjId(12) -> obj_12_result
```

The shorter object spelling is unambiguous beside the deliberately explicit
`well_defined_fact_N` audit names.

One source occurrence and one fixed object are different identities. Every
compound-object occurrence records the exact `WellDefinedObjId` it used. A
cache miss creates a new object identity after all child objects and direct WD
facts succeed. A cache hit records another occurrence use of the existing
identity and must not create or re-render the object.

The object DAG retains typed child roles such as function prefix, function
argument, left operand, and right operand. Thus `g(1)(2)` first fixes `g(1)`
as its own `obj_K`; the outer object cites `obj_K` through a `FunctionPrefix`
edge and uses `obj_K_result` as the second-layer function-space membership.
An unordered vector of child IDs is insufficient:
the Lean emitter must never guess construction positions from source text.
Object and fact nodes form one dependency DAG because their dependencies can
alternate:

```text
argument membership
  -> applicable proof
  -> fixed application object
  -> result membership
  -> outer applicable proof
  -> fixed outer application object
```

The emitter owns one cross-statement registry from `WellDefinedObjId` to its
already emitted Lean declaration. In a parameterized Lean theorem, that
declaration is generalized over exactly the visible binders needed by the
compiled object and is applied back to the current fixed arguments. A later
use of the same accessible Litex cache identity cites that declaration; it
does not reconstruct the application from rendered text.

This guarantee applies to object nodes retained in the successful statement's
frozen certificate (and their transitive children). Speculative candidate
search environments that Litex rolls back are deliberately absent and emit
nothing.

Visibility follows Litex environments. Children see parent objects; discarded
child objects do not leak; committed child identities merge under the same
rules as the runtime cache. Cache identity includes the exact callable
contract `FactId`, so reinstalling a function-space membership creates a new
`WellDefinedObjId` even when the printed application text is unchanged.

## 10. Semantic core, ordinary theorems, and trust

Only the small interpretation boundary may be axiomatic: the object universe,
membership, restricted object constructors, numeric embedding, and the exact
function/application boundary.

Each concrete verifier builtin rule is a real Lean theorem under
`Litex.BuiltinRules`, proved once in the shared Lake library from that core and
Mathlib. A compiler certificate validates the rule ID, target, ordered child
facts, and substitution shape before calling that theorem. It does not repeat
the theorem proof at the use site or turn the successful builtin use into
another axiom.

Only explicit source `trust` may produce a target axiom for the trusted
proposition. Unsupported statements, missing WD IDs, stale function contracts,
and malformed certificates fail closed; they do not produce `sorry`, proof
search, or implicit axioms.

## Current generated file prefix

Every successful generated source currently has this shape:

```text
import Litex.BuiltinRules

example : Litex.abiVersion = 7 := rfl

<WD helper declarations and translated source declarations>
```

The checked-in generated header is
[`current_generated_file_header.lean`](current_generated_file_header.lean).
The complete numeric/function declarations and builtin theorem bodies live
only in the shared library. `lean/Litex/Core.lean` is therefore the snapshot
that exposes the `IsSet` and constructor-WD implementation debts described
above.

## Ten representative examples

The Lean blocks below show the required shape, not stable generated identifier
numbers. A name such as `well_defined_fact_17` stands for the exact helper
selected by the verifier-owned ID.

### Example 1 — standard set, user set, and set parameter

Status: **Current**, except that `IsSet` is still opaque in the shared core.

```litex
forall S set, a R, b S:
    a = a
    b = b
```

Required target binder shape:

```lean
∀ (S : Litex.Object)
  (hS : Litex.IsSet S)
  (a : Litex.Object)
  (haR : Litex.In a Litex.R)
  (b : Litex.Object)
  (hbS : Litex.In b S),
  a = a ∧ b = b
```

`R` and `S` are both objects. Neither becomes a Lean carrier.

### Example 2 — one object with both `C` and `R` membership

Status: **Current** and the primary tracer.

```litex
forall a C, f fn(x R) R:
    a = 1
    =>:
        1 $in R
        a $in R
        f(a) = f(a)
```

Required target facts and call:

```lean
(a : Litex.Object)
(haC : Litex.In a Litex.C)
(haR : Litex.In a Litex.R)
(hf : Litex.In f (Litex.FnSet spec))

f [a]
  (Litex.fnSetApplicable hf rfl haR)
```

The same `a` retains both memberships. Without the exact proof `haR`, Litex
rejects `f(a)` and To-Lean emits no call.

### Example 3 — one numeral and the one complex addition

Status: **Current** for the numeral object and proof-carrying addition.

```litex
forall a, b R:
    a + b $in R
```

The target constructor and real-closure theorem both consume the exact complex
membership proofs selected from the WD DAG:

```lean
Litex.add a b haC hbC

Litex.BuiltinRules.realAddClosure haC hbC haR hbR :
  Litex.In (Litex.add a b haC hbC) Litex.R
```

There is no separate real `+`. Both operands are also known to be in `C`, and
the source `+` denotes the single complex addition.

### Example 4 — a unary function-space membership

Status: **Current**.

```litex
forall f fn(x R) R:
    f(2) = f(2)
```

Conceptual function-space object and call:

```lean
let spec : Litex.FnSpec := {
  arity := 1
  requirements := fun args => Litex.In (Litex.arg args 0) Litex.R
  range := fun _ => Litex.R
}

hf : Litex.In f (Litex.FnSet spec)

f [2]
  (Litex.fnSetApplicable hf rfl
    (Litex.BuiltinRules.numeralInR 2))
```

The membership `hf`, not the Lean type of `f`, says which function contract is
being used.

### Example 5 — a refined domain rejects an illegal call

Status: **Current architecture**; broader comparison emission remains part of
the builtin-porting work.

```litex
forall f fn(x R: x > 0) R:
    f(2) = f(2)
```

The applicability proof contains every ordered requirement:

```lean
have h2R : Litex.In (2 : Litex.Object) Litex.R := ...
have h2Pos : Litex.gt (2 : Litex.Object) 0 := ...
have happ : Litex.Applicable f [2] :=
  Litex.fnSetApplicable hf rfl ⟨h2R, h2Pos⟩

exact f [2] happ
```

For `f(-1)`, the compiler cannot manufacture the positive-domain fact, so the
source remains rejected even though `-1` may have real membership.

### Example 6 — one three-argument application layer

Status: **Current**.

```litex
forall f fn(x, y, z R) R:
    f(1, 2, 3) = f(1, 2, 3)
```

Required target shape:

```lean
noncomputable def obj_1 : Litex.Object := 1
noncomputable def obj_2 : Litex.Object := 2
noncomputable def obj_3 : Litex.Object := 3
noncomputable def obj_4 : Litex.Object :=
  f [obj_1, obj_2, obj_3] obj_4_applicable
```

The one source group remains one list. A split expression such as
`f(1)(2, 3)` is not repaired by Lean currying and remains rejected for this
single-layer contract.

### Example 7 — a function-valued result creates a second layer

Status: **Current**.

```litex
forall g fn(x R) fn(y R) R:
    g(1)(2) = g(1)(2)
```

Required target shape:

```lean
noncomputable def obj_40 : Litex.Object := g [obj_1] obj_40_applicable
theorem obj_40_result : Litex.In obj_40 innerFnSet :=
  Litex.fnSetResult hf rfl first_requirements
noncomputable def obj_41 : Litex.Object :=
  obj_40 [obj_2] obj_41_applicable
```

The two `Applicable` proofs are distinct. This is not identified with one call
`g [1, 2] ...`.

### Example 8 — mixed and dependent parameter requirements

Status: **Decided**; full dependent non-function return-set emission remains
in the compiler backlog.

```litex
abstract_prop p(x, y)

forall S set, f fn(x R, y S: x > 0, $p(x, y)) R:
    forall a R, b S:
        a > 0
        $p(a, b)
        =>:
            f(a, b) = f(a, b)
```

The `FnSpec` requirement for `[a, b]` is ordered and contains all four facts:

```lean
Litex.In a Litex.R ∧
Litex.In b S ∧
Litex.gt a 0 ∧
p a b
```

The call cites those exact facts. Proving later that `b` belongs to another set
does not replace or cast `b`, and it does not change which `FnSpec` this call
uses.

### Example 9 — an anonymous function carries body and range WD

Status: **Decided**, not emitted yet; exact constructor spelling is open.

```litex
fn(x, y R: x < y) R {x + y}
```

The target object must carry a certificate equivalent to:

```lean
have hBody :
    ∀ args,
      args.length = 2 →
      spec.requirements args →
      Litex.In (body args) Litex.R := by
  -- Replays the retained WD DAG for x + y and real closure.
  ...

Litex.anonymousFn spec body hBody
```

The domain facts justify construction of the body, and `hBody` proves that the
result belongs to the declared range. The compiler may not emit an unguarded
Lean lambda that is meaningful outside the source domain.

### Example 10 — proof-carrying list set and replacement

Status: list sets are **current in ABI version 7**; replacement remains
**decided, not emitted yet**.

```litex
{a, b}
replacement(P, A)
```

Required target shape:

```lean
noncomputable def obj_54 : Litex.Object :=
  Litex.listSet [obj_51, obj_52] (by
    apply List.Pairwise.cons
    · intro x hx
      ...
      exact well_defined_fact_53
    · ...)

have hUnique : Litex.ReplacementWellDefined P A :=
  well_defined_fact_53

let imageSet := Litex.replacement P A hUnique
```

The WD proofs are arguments of the constructed objects, not detached comments.
Their IDs still preserve the exact Litex proof routes. Because the certificate
types are propositions, using a different proof of the same obligation does
not introduce new mathematical data.

## Acceptance boundaries for the next implementation steps

The design is implemented only when all of the following are true:

1. the shared core defines `IsSet` as always true and updates the derived set
   predicates consistently;
2. set extensionality and restricted primitive set constructors have explicit
   semantic laws;
3. every partial object constructor and application consumes its retained WD
   certificate;
4. anonymous functions replay body WD and range membership;
5. all ten examples have executable positive coverage when their source syntax
   is supported, with the nearest invalid domain/application boundary kept as
   a negative regression;
6. the exact generated import header, shared Lake modules, and real Mathlib
   gate pass.
