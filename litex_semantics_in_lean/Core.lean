import Mathlib

/-!
# Litex semantic core

This file is the standalone semantic interface described by the neighbouring
README. It keeps ordinary Lean values in their native carriers and uses
`Same`, `In`, and `IsSet` for Litex meaning. It deliberately does not model
Rust `Obj`, `Stmt`, or `Fact` as a second Lean AST.

The file is a closed core boundary: no project axiom, `sorry`, `admit`, or
unsafe proof is used here. Verifier rules may construct only the reviewed
`ComplexLaw` constructors and the extensionality constructor below.
-/

namespace Litex

universe u v w

/-! ## Exact set carriers -/

structure Set.{u} where
  Carrier : Type u

namespace Set

def ofType (α : Type u) : Set.{u} := ⟨α⟩

end Set

/-! ## Reviewed numeric representation bridges -/

class ComplexView (α : Type u) where
  toComplex : α → ℂ

namespace ComplexView

def nat : ComplexView ℕ := ⟨fun n => (n : ℂ)⟩
def int : ComplexView ℤ := ⟨fun z => (z : ℂ)⟩
def rat : ComplexView ℚ := ⟨fun q => (q : ℂ)⟩
def real : ComplexView ℝ := ⟨fun r => (r : ℂ)⟩
def complex : ComplexView ℂ := ⟨id⟩

end ComplexView

instance : ComplexView ℕ := ComplexView.nat
instance : ComplexView ℤ := ComplexView.int
instance : ComplexView ℚ := ComplexView.rat
instance : ComplexView ℝ := ComplexView.real
instance : ComplexView ℂ := ComplexView.complex

/-!
`ComplexLaw` is intentionally closed. Its constructors are the reviewed
native numeric representation edges; arbitrary relations cannot be registered
by constructing a value of this type.
-/
inductive ComplexLaw :
    {α : Type u} → {β : Type v} → α → β → Prop where
  | natComplex (n : ℕ) : ComplexLaw n (n : ℂ)
  | intComplex (z : ℤ) : ComplexLaw z (z : ℂ)
  | ratComplex (q : ℚ) : ComplexLaw q (q : ℂ)
  | realComplex (r : ℝ) : ComplexLaw r (r : ℂ)

/-!
`Same` is heterogeneous semantic equality. `ofSetExt` uses the exact
membership formula directly, so the inductive definition remains closed while
`In` can expose the same formula as its public interface below.
-/
inductive Same :
    {α : Type u} → {β : Type v} → α → β → Prop where
  | ofEq {α : Type u} {x y : α} : x = y → Same x y
  | ofComplexLaw {α : Type u} {β : Type v} {x : α} {y : β} :
      ComplexLaw x y → Same x y
  | refl {α : Type u} (x : α) : Same x x
  | symm {α : Type u} {β : Type v} {x : α} {y : β} :
      Same x y → Same y x
  | trans {α : Type u} {β : Type v} {γ : Type w}
      {x : α} {y : β} {z : γ} :
      Same x y → Same y z → Same x z
  | ofSetExt {A : Set.{u}} {B : Set.{v}} :
      (∀ {γ : Type w} (x : γ),
        (∃ a : A.Carrier, Same x a) ↔
        (∃ b : B.Carrier, Same x b)) →
      Same A B

/-! ## Membership and set views -/

def In {α : Type u} (x : α) (S : Set.{v}) : Prop :=
  ∃ y : S.Carrier, Same x y

structure SetView {α : Type u} (value : α) where
  set : Set.{v}
  same : Same value set

/-
`IsSet` records a set view in the value's universe. `SetView` remains
universe-polymorphic for callers that need a different exact carrier; the
explicit `SetView` value is the evidence in that case.
-/
def IsSet {α : Type u} (value : α) : Prop :=
  ∃ S : Set.{u}, Same value S

def SetExtensional (A : Set.{u}) (B : Set.{v}) : Prop :=
  ∀ {γ : Type w} (x : γ), In x A ↔ In x B

namespace Same

theorem ofEq' {α : Type u} {x y : α} (h : x = y) : Same x y :=
  .ofEq h

theorem ofComplexLaw' {α : Type u} {β : Type v} {x : α} {y : β}
    (h : ComplexLaw x y) : Same x y :=
  .ofComplexLaw h

theorem ofSetExt {A : Set.{u}} {B : Set.{v}}
    (h : SetExtensional A B) : Same A B := by
  apply .ofSetExt
  intro γ x
  simpa [In] using h x

theorem complexLaw_nat (n : ℕ) : Same n (n : ℂ) :=
  .ofComplexLaw (.natComplex n)

theorem complexLaw_int (z : ℤ) : Same z (z : ℂ) :=
  .ofComplexLaw (.intComplex z)

theorem complexLaw_rat (q : ℚ) : Same q (q : ℂ) :=
  .ofComplexLaw (.ratComplex q)

theorem complexLaw_real (r : ℝ) : Same r (r : ℂ) :=
  .ofComplexLaw (.realComplex r)

end Same

namespace In

theorem iff_rep {α : Type u} (x : α) (S : Set.{v}) :
    In x S ↔ ∃ y : S.Carrier, Same x y := Iff.rfl

theorem ofSame {α : Type u} {β : Type v} {x : α} {y : β} {S : Set.{w}}
    (hy : In y S) (hxy : Same x y) : In x S := by
  rcases hy with ⟨z, hyz⟩
  exact ⟨z, Same.trans hxy hyz⟩

theorem congr {α : Type u} {β : Type v} {x : α} {y : β} {S : Set.{w}}
    (hxy : Same x y) : In x S ↔ In y S := by
  constructor
  · intro hx
    exact ofSame hx (Same.symm hxy)
  · intro hy
    exact ofSame hy hxy

end In

namespace SetView

theorem same {α : Type u} {value : α} (view : SetView value) :
    Same value view.set := view.same

end SetView

/-! ## Complex observations and native adapter bridges -/

def ComplexView.RespectsSame
    {α : Type u} {β : Type v}
    (viewA : ComplexView α) (viewB : ComplexView β) : Prop :=
  ∀ {x : α} {y : β}, Same x y →
    viewA.toComplex x = viewB.toComplex y

theorem same_observation_eq
    {α : Type u} {β : Type v}
    (viewA : ComplexView α) (viewB : ComplexView β)
    {x : α} {y : β} (h : Same x y)
    (respects : ComplexView.RespectsSame viewA viewB) :
    viewA.toComplex x = viewB.toComplex y :=
  respects h

theorem Same.complexEq
    {α : Type u} {β : Type v}
    [viewA : ComplexView α] [viewB : ComplexView β]
    {x : α} {y : β} (h : Same x y)
    (respects : ComplexView.RespectsSame viewA viewB) :
    viewA.toComplex x = viewB.toComplex y :=
  same_observation_eq viewA viewB h respects

theorem same_of_complex_eq
    {x y : ℂ} (h : x = y) : Same x y :=
  Same.ofEq h

theorem same_real_cast (r : ℝ) : Same r (r : ℂ) :=
  Same.complexLaw_real r

theorem same_nat_cast (n : ℕ) : Same n (n : ℂ) :=
  Same.complexLaw_nat n

/- A faithful observation recovers native equality only with its explicit
injectivity and observation-compatibility evidence. `Same` itself is never
treated as a global Lean `Eq` rewrite rule.
-/
theorem nativeEq_of_observation
    {α : Type u} {x y : α}
    (view : ComplexView α)
    (injective : Function.Injective view.toComplex)
    (h : Same x y)
    (respects : ∀ {a b : α}, Same a b →
      view.toComplex a = view.toComplex b) :
    x = y := by
  apply injective
  exact respects h

end Litex

/-! ## Standard sets and a small checked vertical slice -/

namespace Litex

def N : Set := Set.ofType ℕ
def Z : Set := Set.ofType ℤ
def Q : Set := Set.ofType ℚ
def R : Set := Set.ofType ℝ
def C : Set := Set.ofType ℂ

theorem nat_mem_Z (n : ℕ) : In (n : ℕ) Z := by
  exact ⟨(n : ℤ), Same.trans (Same.ofEq (by rfl)) (Same.complexLaw_int (n : ℤ))⟩

theorem same_two_forms : Same (3 : ℕ) (3 : ℂ) :=
  Same.complexLaw_nat 3

theorem complex_add_example : Same ((1 : ℂ) + 1) 2 := by
  apply Same.ofEq
  norm_num

theorem set_extensional_reflexive (S : Set) : Same S S :=
  Same.refl S

end Litex
