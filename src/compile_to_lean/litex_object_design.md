# Universal `LitexObject` design

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

The exact prefix emitted by the compiler today is checked in as
[`current_generated_file_header.lean`](current_generated_file_header.lean).
`universal_prelude.rs` remains the implementation source of truth, and a Rust
test requires the checked-in header to match it exactly.

## 1. One universe of objects

Every Litex object lowers to one Lean type:

```lean
axiom LitexObject : Type
```

This includes:

- ordinary values;
- user-defined sets;
- `N`, `Z`, `Q`, `R`, `C`, and their refined subsets;
- function-space objects such as `fn(x R) R`;
- function values;
- objects produced by function calls;
- list sets, replacement sets, and other set constructors.

There is no `LitexObject α`, carrier inference, native binder such as
`x : ℝ`, widening, downcast, or conversion between memberships. Lean equality
on `LitexObject` is Litex object equality.

## 2. Every object is a set; membership is independent

The decided set foundation is:

```lean
axiom Litex.In : LitexObject → LitexObject → Prop

def Litex.IsSet (_ : LitexObject) : Prop := True

def Litex.IsNonemptySet (s : LitexObject) : Prop :=
  ∃ x : LitexObject, Litex.In x s

def Litex.IsFiniteSet (s : LitexObject) : Prop :=
  Set.Finite {x : LitexObject | Litex.In x s}
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
axiom Litex.ext {A B : LitexObject} :
  (∀ x : LitexObject, Litex.In x A ↔ Litex.In x B) → A = B
```

This does not license unrestricted comprehension. There must be no constructor
of the form

```lean
-- forbidden
setOf : (LitexObject → Prop) → LitexObject
```

with an unrestricted membership equivalence. Source set builders must use a
restricted source contract, and partial constructors must carry their Litex
well-definedness certificate.

### Current implementation drift

The current generated header still contains:

```lean
axiom Litex.IsSet : LitexObject → Prop
```

and derives nonemptiness and finiteness with an `IsSet` conjunct. Replacing
that declaration with the always-true definition above is decided but not yet
implemented. The exact current header is preserved separately so this debt is
visible instead of silently rewritten in documentation.

## 3. Standard numeric sets and one numeral object

Every standard numeric domain is a `LitexObject`:

```lean
axiom Litex.N : LitexObject
axiom Litex.Z : LitexObject
axiom Litex.Q : LitexObject
axiom Litex.R : LitexObject
axiom Litex.C : LitexObject
```

Refined domains such as `N+`, `Z*`, `R+`, and `R*` are additional set objects,
not Lean subtypes. They are emitted in the common file header whether or not a
particular source file mentions them.

An Arabic numeral denotes one object. The current bridge embeds Mathlib
complex numbers:

```lean
axiom Litex.embedComplex : ℂ → LitexObject

instance (n : Nat) : OfNat LitexObject n where
  ofNat := Litex.embedComplex (n : ℂ)
```

Separate theorems establish memberships such as `1 ∈ N`, `1 ∈ R`, and
`1 ∈ C`. Those theorems do not create three different objects.

Litex does not overload source `+`. Every source occurrence denotes the one
Litex complex addition operation. Real or integer closure is justified by
ordinary builtin-rule theorems using retained membership proofs. The current
header exposes total `Litex.add/sub/mul/div` primitives. Under the decided WD
rule, a future final ABI must also prevent the compiler from constructing a
source arithmetic object without its required domain certificate. Whether
builtins use generic `Applicable` or constructor-specific applicability
predicates is still **open spelling**; erasing the certificate is not open.

## 4. Function spaces are set objects

One source function layer is described by a restricted specification:

```lean
structure Litex.FnSpec where
  arity : Nat
  requirements : List LitexObject → Prop
  range : List LitexObject → LitexObject

axiom Litex.FnSet : Litex.FnSpec → LitexObject
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
  LitexObject → List LitexObject → Prop

axiom Litex.apply :
  (f : LitexObject) →
  (args : List LitexObject) →
  Litex.Applicable f args →
  LitexObject
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
    {f : LitexObject} {spec : Litex.FnSpec}
    {args : List LitexObject} :
  Litex.In f (Litex.FnSet spec) →
  args.length = spec.arity →
  spec.requirements args →
  Litex.Applicable f args

axiom Litex.fnSetResult
    {f : LitexObject} {spec : Litex.FnSpec}
    {args : List LitexObject}
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
def Litex.ListSetWellDefined (xs : List LitexObject) : Prop :=
  xs.Pairwise (· ≠ ·)

axiom Litex.listSet :
  (xs : List LitexObject) →
  Litex.ListSetWellDefined xs →
  LitexObject

def Litex.ReplacementWellDefined
    (P : LitexObject → LitexObject → Prop)
    (A : LitexObject) : Prop :=
  ∀ x, Litex.In x A →
    ∀ y₁ y₂, P x y₁ → P x y₂ → y₁ = y₂

axiom Litex.replacement :
  (P : LitexObject → LitexObject → Prop) →
  (A : LitexObject) →
  Litex.ReplacementWellDefined P A →
  LitexObject
```

These declarations are **decided semantic shapes**, but their exact names are
not implemented in the current prelude yet.

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
    (body : List LitexObject → LitexObject) : Prop :=
  ∀ args,
    args.length = spec.arity →
    spec.requirements args →
    Litex.In (body args) (spec.range args)

axiom Litex.anonymousFn :
  (spec : Litex.FnSpec) →
  (body : List LitexObject → LitexObject) →
  Litex.AnonymousFnWellDefined spec body →
  LitexObject
```

If constructing `body args` itself needs the requirement proof, the final Lean
field must take that proof as an argument. The compiler may not totalize an
undefined source body merely to fit the simpler sketch above.

## 8. Set constructors and semantic laws

Total primitive set operations may be ordinary object constructors:

```lean
axiom Litex.empty : LitexObject
axiom Litex.union : LitexObject → LitexObject → LitexObject
axiom Litex.intersect : LitexObject → LitexObject → LitexObject
axiom Litex.setMinus : LitexObject → LitexObject → LitexObject
axiom Litex.powerSet : LitexObject → LitexObject
```

Their membership meanings belong to the small semantic core:

```lean
axiom Litex.inEmpty_iff {x : LitexObject} :
  ¬ Litex.In x Litex.empty

axiom Litex.inUnion_iff {x A B : LitexObject} :
  Litex.In x (Litex.union A B) ↔ Litex.In x A ∨ Litex.In x B

axiom Litex.inIntersect_iff {x A B : LitexObject} :
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
    {x : LitexObject} {xs : List LitexObject}
    {h : Litex.ListSetWellDefined xs} :
  Litex.In x (Litex.listSet xs h) ↔ x ∈ xs
```

## 9. Verifier-owned identities and replay order

The Lean emitter does not re-run Litex verification or search for an equivalent
target proof. The verifier freezes:

- `SourceObjectOccurrenceId` for each source occurrence;
- `FactId` for every environment-stored fact;
- `WellDefinedObjProofId` for each node of the object-WD DAG;
- `WellDefinedFactId` for each factual obligation used by that DAG;
- direct child edges, target requirement roles, source scope, and the exact
  function-space membership contract.

Lean declarations use stable names such as:

```lean
theorem well_defined_fact_17 ... : Litex.In a Litex.R := ...
```

Children are emitted before parents. If the proof is needed in another
theorem's type, its helper is emitted before that theorem and generalized over
the visible Litex environment. A WD cache hit cites the original accessible
ID; it does not become a proofless boolean. Child environments see parent
facts, discarded child facts do not leak, and committed scopes follow the
runtime's real merge rules.

## 10. Semantic core, ordinary theorems, and trust

Only the small interpretation boundary may be axiomatic: the object universe,
membership, restricted object constructors, numeric embedding, and the exact
function/application boundary.

Each concrete verifier builtin rule is a real Lean theorem under
`Litex.BuiltinRules`, proved once from that core and Mathlib. A compiler
certificate validates the rule shape and calls that theorem. It does not turn
the successful builtin use into another axiom.

Only explicit source `trust` may produce a target axiom for the trusted
proposition. Unsupported statements, missing WD IDs, stale function contracts,
and malformed certificates fail closed; they do not produce `sorry`, proof
search, or implicit axioms.

## Current generated file prefix

Every successful generated source currently has this shape:

```text
import Mathlib

<the exact contents returned by universal_object_prelude()>

<WD helper declarations and translated source declarations>
```

The complete checked-in prefix, including all current numeric and function
declarations and builtin theorems, is
[`current_generated_file_header.lean`](current_generated_file_header.lean).
It is intentionally an implementation snapshot, so it still shows the
`IsSet` and constructor-WD implementation debts described above.

## Ten representative examples

The Lean blocks below show the required shape, not stable generated identifier
numbers. A name such as `well_defined_fact_17` stands for the exact helper
selected by the verifier-owned ID.

### Example 1 — standard set, user set, and set parameter

Status: **Current**, except that `IsSet` is still opaque in the emitted header.

```litex
forall S set, a R, b S:
    a = a
    b = b
```

Required target binder shape:

```lean
∀ (S : LitexObject)
  (hS : Litex.IsSet S)
  (a : LitexObject)
  (haR : Litex.In a Litex.R)
  (b : LitexObject)
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
(a : LitexObject)
(haC : Litex.In a Litex.C)
(haR : Litex.In a Litex.R)
(hf : Litex.In f (Litex.FnSet spec))

f [a]
  (Litex.fnSetApplicable hf rfl haR)
```

The same `a` retains both memberships. Without the exact proof `haR`, Litex
rejects `f(a)` and To-Lean emits no call.

### Example 3 — one numeral and the one complex addition

Status: **Current** for the numeral object and current total arithmetic
primitive; **Decided** that final partial-operation terms retain WD.

```litex
forall a, b R:
    a + b $in R
```

Current target core uses one operation and proves real closure:

```lean
Litex.BuiltinRules.realAddClosure haR hbR :
  Litex.In (Litex.add a b) Litex.R
```

There is no separate real `+`. Both operands are also known to be in `C`, and
the source `+` denotes the single complex addition. The final proof-carrying
operation spelling is still to be frozen.

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
have h2R : Litex.In (2 : LitexObject) Litex.R := ...
have h2Pos : Litex.gt (2 : LitexObject) 0 := ...
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
f [1, 2, 3] well_defined_fact_31
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
let first := g [1] well_defined_fact_40
have hFirstFn : Litex.In first innerFnSet :=
  Litex.fnSetResult hf rfl first_requirements
let result := first [2] well_defined_fact_41
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

Status: **Decided**, not emitted yet.

```litex
{a, b}
replacement(P, A)
```

Required target shape:

```lean
have hDistinct : Litex.ListSetWellDefined [a, b] :=
  well_defined_fact_52

have hUnique : Litex.ReplacementWellDefined P A :=
  well_defined_fact_53

let pairSet := Litex.listSet [a, b] hDistinct
let imageSet := Litex.replacement P A hUnique
```

The WD proofs are arguments of the constructed objects, not detached comments.
Their IDs still preserve the exact Litex proof routes. Because the certificate
types are propositions, using a different proof of the same obligation does
not introduce new mathematical data.

## Acceptance boundaries for the next implementation steps

The design is implemented only when all of the following are true:

1. the generated header defines `IsSet` as always true and updates the derived
   set predicates consistently;
2. set extensionality and restricted primitive set constructors have explicit
   semantic laws;
3. every partial object constructor and application consumes its retained WD
   certificate;
4. anonymous functions replay body WD and range membership;
5. all ten examples have executable positive coverage when their source syntax
   is supported, with the nearest invalid domain/application boundary kept as
   a negative regression;
6. the exact generated header snapshot and real Mathlib gate pass.
