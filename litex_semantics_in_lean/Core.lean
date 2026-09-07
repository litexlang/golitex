import Mathlib

/-!
# Litex semantic core contract

This is a new, standalone design repository. It does not import the old
`lean/Litex/Core.lean`; the old tree is an implementation baseline only.

The central choice is to make one `World` carry the semantic relations and
their proof obligations. The world has a type of set expressions, but it has
no type containing all Litex objects. Ordinary values remain ordinary Lean
terms (`x : α`). The only cross-carrier identity is `World.Same`.

`Gt` is a primitive Litex proposition in this contract. It is intentionally
not defined as `RealPos`, an existential over real representatives, or a
`Complex.re` comparison. The world supplies checked elimination and
introduction bridges for the real ordered fragment. A builtin rule may use
those bridges internally and call Mathlib, while its public conclusion remains
`World.Gt ...`.

The first prototype fixes host carriers at Lean's universe-zero `Type`. The
production ABI should generalize the same fields over universe parameters;
that is an ABI extension after semantic ownership is settled.
-/

namespace LitexSemanticsInLean

/-! ## The semantic world

`SetExpr` is only the type of Litex set expressions. It is not a universal
object box: ordinary numeric values, functions, tuples, matrices, and
structures continue to use their own Lean carriers. `carrier S` is the exact
native carrier selected for a set expression `S`.
-/
structure World where
  SetExpr : Type
  carrier : SetExpr → Type

  /-- Heterogeneous Litex identity, deliberately wider than Lean `Eq`. -/
  Same : {α β : Type} → α → β → Prop

  /-- Heterogeneous membership. Its exact contract is `in_iff` below. -/
  In : {α : Type} → α → SetExpr → Prop

  /-- A value may have set semantics without having host type `SetExpr`. -/
  IsSet : {α : Type} → α → Prop

  /-- The Litex order relation printed by generated source theorems. -/
  Gt : {α β : Type} → α → β → Prop

  /-- Numeric operations used by the tracer rule. -/
  zero : ℂ
  add : ℂ → ℂ → ℂ
  R : SetExpr

  /-- Lean equality is always a valid Litex identity edge. -/
  same_of_eq : {α : Type} → {x y : α} → x = y → Same x y

  /-- The identity relation is an equivalence relation. -/
  same_refl : {α : Type} → (x : α) → Same x x
  same_symm : {α β : Type} → {x : α} → {y : β} → Same x y → Same y x
  same_trans : {α β γ : Type} → {x : α} → {y : β} → {z : γ} →
    Same x y → Same y z → Same x z

  /-- The single membership contract. A compiler proof may open `In` only by
  this named bridge, obtaining an exact-carrier representative. -/
  in_iff : {α : Type} → (x : α) → (S : SetExpr) →
    In x S ↔ ∃ y : carrier S, Same x y

  /-- A set view connects a non-set-typed value to an exact set expression. -/
  isSet_iff : {α : Type} → (x : α) →
    IsSet x ↔ ∃ S : SetExpr, Same x S

  /-- The set extension axiom at the Litex boundary. -/
  same_of_set_ext : {A B : SetExpr} →
    (∀ {α : Type} (x : α), In x A ↔ In x B) → Same A B

  /-- Addition is semantically congruent with checked native real
  representatives. This is a closed complex/arithmetic bridge. -/
  same_add_real : {a b : ℂ} → {ar br : ℝ} →
    Same a (ar : ℂ) → Same b (br : ℂ) →
    Same (add a b) ((ar + br : ℝ) : ℂ)

  /-- Verifier-owned well-definedness for an additive result. -/
  add_mem_R : {a b : ℂ} → In a R → In b R → In (add a b) R

  /-- Unwrap a Litex `a > 0` fact only inside a reviewed adapter. -/
  gt_zero_to_real : {a : ℂ} →
    In a R → Gt a zero →
    ∃ ar : ℝ, Same a (ar : ℂ) ∧ 0 < ar

  /-- Wrap a native real positivity proof back into Litex `Gt`. -/
  gt_zero_of_real : {a : ℂ} →
    In a R → (∃ ar : ℝ, Same a (ar : ℂ) ∧ 0 < ar) → Gt a zero

/-! ## Evidence names crossing the Rust/Lean boundary -/

/- A FactId is an identity key, not a proposition string. The Rust Result
tree owns its numbering and the compiler uses this key for exact citations. -/
structure FactId where
  value : Nat
deriving Repr, DecidableEq

/- The proposition family is intentionally small and compositional. Concrete
facts carry their Litex proposition and proof in `FactResult`; logical
connectives remain ordinary Lean propositions around these atoms. -/
inductive FactShape where
  | same
  | membership
  | sethood
  | greaterThan
  | logical
deriving Repr, DecidableEq

structure FactResult (shape : FactShape) where
  id : FactId
  proposition : Prop
  proof : proposition

/- Statement execution has declaration and scope effects in addition to a
fact proof. This record is metadata for the compiler contract, not a second
proof-search tree. -/
structure StmtEffect where
  sourceName : String
  declarations : List String
  publishedFacts : List FactId
  localFacts : List FactId

namespace API

/-! ## Stable names used by the compiler and adapter

These are projections, not a second semantic IR. Rust `Obj`/`Fact`/`Stmt`
results choose which projection is needed and carry verifier evidence that
discharges its fields.
-/

abbrev Set (W : World) := W.SetExpr
abbrev SemanticSame (W : World) {α β : Type} (x : α) (y : β) : Prop :=
  W.Same x y
abbrev Membership (W : World) {α : Type} (x : α) (S : W.SetExpr) : Prop :=
  W.In x S
abbrev Sethood (W : World) {α : Type} (x : α) : Prop := W.IsSet x
abbrev GreaterThan (W : World) {α β : Type} (x : α) (y : β) : Prop :=
  W.Gt x y

def SetExtensional (W : World) (A B : W.SetExpr) : Prop :=
  ∀ {α : Type} (x : α), W.In x A ↔ W.In x B

theorem same_of_set_ext (W : World) {A B : W.SetExpr}
    (h : SetExtensional W A B) : W.Same A B :=
  W.same_of_set_ext h

theorem same_of_eq (W : World) {α : Type} {x y : α} (h : x = y) :
    W.Same x y :=
  W.same_of_eq h

theorem same_refl (W : World) {α : Type} (x : α) : W.Same x x :=
  W.same_refl x

theorem same_symm (W : World) {α β : Type} {x : α} {y : β}
    (h : W.Same x y) : W.Same y x :=
  W.same_symm h

theorem same_trans (W : World) {α β γ : Type}
    {x : α} {y : β} {z : γ}
    (hxy : W.Same x y) (hyz : W.Same y z) : W.Same x z :=
  W.same_trans hxy hyz

theorem in_iff (W : World) {α : Type} (x : α) (S : W.SetExpr) :
    W.In x S ↔ ∃ y : W.carrier S, W.Same x y :=
  W.in_iff x S

theorem isSet_iff (W : World) {α : Type} (x : α) :
    W.IsSet x ↔ ∃ S : W.SetExpr, W.Same x S :=
  W.isSet_iff x

/- A retained set view is the exact evidence needed by `forall A set`,
`have A set`, and set-valued object lowering. -/
structure SetView (W : World) {α : Type} (value : α) where
  set : W.SetExpr
  same : W.Same value set

noncomputable def setView (W : World) {α : Type} {value : α}
    (h : W.IsSet value) : SetView W value := by
  let witnesses := (W.isSet_iff value).mp h
  exact ⟨Classical.choose witnesses, Classical.choose_spec witnesses⟩

noncomputable def setRep (W : World) {α : Type} {value : α}
    (h : W.IsSet value) : W.SetExpr :=
  (setView W h).set

theorem setRep_same (W : World) {α : Type} {value : α}
    (h : W.IsSet value) : W.Same value (setRep W h) :=
  (setView W h).same

/- `In` is never a type cast. This helper exposes a carrier witness only when
a verifier-owned membership proof explicitly requests it. -/
theorem in_rep (W : World) {α : Type} {x : α} {S : W.SetExpr}
    (hx : W.In x S) : ∃ y : W.carrier S, W.Same x y :=
  (W.in_iff x S).mp hx

/-! ## Thin native bridges -/

theorem same_complex_native_eq (W : World) {x y : ℂ}
    (h : W.Same x y)
    (native : ∀ {a b : ℂ}, W.Same a b → a = b) : x = y :=
  native h

/- The adapter supplies a carrier-specific observation and its checked
coherence proof. The theorem itself does not enlarge `Same`. -/
structure ComplexView (W : World) (α : Type) where
  toComplex : α → ℂ

def ComplexView.RespectsSame (W : World)
    {α β : Type} (viewA : ComplexView W α) (viewB : ComplexView W β) : Prop :=
  ∀ {x : α} {y : β}, W.Same x y →
    viewA.toComplex x = viewB.toComplex y

theorem same_observation_eq (W : World)
    {α β : Type} (viewA : ComplexView W α) (viewB : ComplexView W β)
    {x : α} {y : β} (h : W.Same x y)
    (respects : ComplexView.RespectsSame W viewA viewB) :
    viewA.toComplex x = viewB.toComplex y :=
  respects h

def natComplexView (W : World) : ComplexView W ℕ :=
  ⟨fun n => (n : ℂ)⟩

def intComplexView (W : World) : ComplexView W ℤ :=
  ⟨fun z => (z : ℂ)⟩

def ratComplexView (W : World) : ComplexView W ℚ :=
  ⟨fun q => (q : ℂ)⟩

def realComplexView (W : World) : ComplexView W ℝ :=
  ⟨fun r => (r : ℂ)⟩

def complexComplexView (W : World) : ComplexView W ℂ :=
  ⟨fun z => z⟩

/-! ## The public order boundary -/

abbrev ComplexGt (W : World) (a b : ℂ) : Prop := W.Gt a b

theorem gt_zero_to_real (W : World) {a : ℂ}
    (ha : W.In a W.R) (h : W.Gt a W.zero) :
    ∃ ar : ℝ, W.Same a (ar : ℂ) ∧ 0 < ar :=
  W.gt_zero_to_real ha h

theorem gt_zero_of_real (W : World) {a : ℂ}
    (ha : W.In a W.R)
    (h : ∃ ar : ℝ, W.Same a (ar : ℂ) ∧ 0 < ar) : W.Gt a W.zero :=
  W.gt_zero_of_real ha h

end API

end LitexSemanticsInLean
