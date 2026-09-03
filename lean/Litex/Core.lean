import Mathlib

namespace Litex

universe u v w x y

/-- The Lean universe used by the v2 public ABI. This is an abbreviation for
Lean's ordinary `Type u`, not a new universe containing Mathlib. -/
abbrev u := Type u

/-- Version of this deliberately incompatible target ABI. -/
def abiVersion : Nat := 2

/-- Exact one-element carrier used by finite Litex set literals. The source
value indexes the type itself, so the carrier cannot contain another value. -/
inductive SingletonCarrier {α : Type u} (value : α) : Type u where
  | element
deriving Fintype

/-- A carrier's canonical partial observation as a native complex value.

The default observer records that a carrier has no numeric observation.  The
five native numeric carriers and the structural wrappers traversed by `Same`
have higher-priority observers below.  Observer values are part of the
proof-level `Same` index: changing an observer does not create a new semantic
equality edge. -/
class ComplexObserver (α : Type u) where
  observe : α → Option ℂ

namespace ComplexObserver

@[reducible] def none (α : Type u) : ComplexObserver α where
  observe _ := Option.none

@[reducible] def nat : ComplexObserver ℕ where
  observe n := some (n : ℂ)

@[reducible] def int : ComplexObserver ℤ where
  observe z := some (z : ℂ)

@[reducible] def rat : ComplexObserver ℚ where
  observe q := some (q : ℂ)

@[reducible] def real : ComplexObserver ℝ where
  observe r := some (r : ℂ)

@[reducible] def complex : ComplexObserver ℂ where
  observe z := some z

@[reducible] def subtype
    {α : Type u}
    {predicate : α → Prop}
    (observer : ComplexObserver α) :
    ComplexObserver (Subtype predicate) where
  observe x := observer.observe x.val

@[reducible] def singleton
    {α : Type u}
    (observer : ComplexObserver α)
    (value : α) :
    ComplexObserver (SingletonCarrier value) where
  observe _ := observer.observe value

@[reducible] def sum
    {α β : Type u}
    (leftObserver : ComplexObserver α)
    (rightObserver : ComplexObserver β) :
    ComplexObserver (Sum α β) where
  observe
    | Sum.inl value => leftObserver.observe value
    | Sum.inr value => rightObserver.observe value

end ComplexObserver

@[reducible] instance (priority := low) defaultComplexObserver
    {α : Type u} : ComplexObserver α :=
  ComplexObserver.none α

@[reducible] instance (priority := high) natComplexObserver :
    ComplexObserver ℕ := ComplexObserver.nat

@[reducible] instance (priority := high) intComplexObserver :
    ComplexObserver ℤ := ComplexObserver.int

@[reducible] instance (priority := high) ratComplexObserver :
    ComplexObserver ℚ := ComplexObserver.rat

@[reducible] instance (priority := high) realComplexObserver :
    ComplexObserver ℝ := ComplexObserver.real

@[reducible] instance (priority := high) complexComplexObserver :
    ComplexObserver ℂ := ComplexObserver.complex

@[reducible] instance (priority := high) subtypeComplexObserver
    {α : Type u}
    {predicate : α → Prop}
    [observer : ComplexObserver α] :
    ComplexObserver (Subtype predicate) :=
  ComplexObserver.subtype observer

@[reducible] instance (priority := high) singletonComplexObserver
    {α : Type u}
    [observer : ComplexObserver α]
    (value : α) :
    ComplexObserver (SingletonCarrier value) :=
  ComplexObserver.singleton observer value

@[reducible] instance (priority := high) sumComplexObserver
    {α β : Type u}
    [leftObserver : ComplexObserver α]
    [rightObserver : ComplexObserver β] :
    ComplexObserver (Sum α β) :=
  ComplexObserver.sum leftObserver rightObserver

/-- Proof-carrying primitive representation edges.

The class is public, but a numeric rule cannot widen semantic equality merely
by choosing `relation := True`: it must also prove that every related pair has
the same selected complex observation. -/
class PrimitiveRule
    (α β : Type u)
    (leftObserver : ComplexObserver α)
    (rightObserver : ComplexObserver β) where
  relation : α → β → Prop
  observationEq {x : α} {y : β} :
    relation x y →
      leftObserver.observe x = rightObserver.observe y

/-- One primitive representation step between values with different (or the
same) Lean carriers at one universe level. -/
def Primitive
    {α β : Type u}
    {leftObserver : ComplexObserver α}
    {rightObserver : ComplexObserver β}
    [rule : PrimitiveRule α β leftObserver rightObserver]
    (x : α)
    (y : β) : Prop :=
  rule.relation x y

/-- Proof-carrying congruence edges. Unlike primitive carrier bridges, these
edges may consume an existing `Same` proof. -/
class DerivedRule
    (α β : Type u)
    (leftObserver : ComplexObserver α)
    (rightObserver : ComplexObserver β) where
  relation : α → β → Prop
  observationEq {x : α} {y : β} :
    relation x y →
      leftObserver.observe x = rightObserver.observe y

def Derived
    {α β : Type u}
    {leftObserver : ComplexObserver α}
    {rightObserver : ComplexObserver β}
    [rule : DerivedRule α β leftObserver rightObserver]
    (x : α)
    (y : β) : Prop :=
  rule.relation x y

instance : PrimitiveRule ℕ ℂ natComplexObserver complexComplexObserver where
  relation n z := z = (n : ℂ)
  observationEq := by rintro n z rfl; rfl

instance : PrimitiveRule ℤ ℂ intComplexObserver complexComplexObserver where
  relation z w := w = (z : ℂ)
  observationEq := by rintro z w rfl; rfl

instance : PrimitiveRule ℚ ℂ ratComplexObserver complexComplexObserver where
  relation q z := z = (q : ℂ)
  observationEq := by rintro q z rfl; rfl

instance : PrimitiveRule ℝ ℂ realComplexObserver complexComplexObserver where
  relation r z := z = (r : ℂ)
  observationEq := by rintro r z rfl; rfl

instance :
    PrimitiveRule ℕ ℂ (ComplexObserver.none ℕ) (ComplexObserver.none ℂ) where
  relation n z := z = (n : ℂ)
  observationEq := by intros; rfl

instance :
    PrimitiveRule ℤ ℂ (ComplexObserver.none ℤ) (ComplexObserver.none ℂ) where
  relation z w := w = (z : ℂ)
  observationEq := by intros; rfl

instance :
    PrimitiveRule ℚ ℂ (ComplexObserver.none ℚ) (ComplexObserver.none ℂ) where
  relation q z := z = (q : ℂ)
  observationEq := by intros; rfl

instance :
    PrimitiveRule ℝ ℂ (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) where
  relation r z := z = (r : ℂ)
  observationEq := by intros; rfl

instance {α : Type u} {predicate : α → Prop}
    [observer : ComplexObserver α] :
    PrimitiveRule (Subtype predicate) α
      (ComplexObserver.subtype observer)
      observer where
  relation x y := y = x.val
  observationEq := by rintro x y rfl; rfl

instance {α : Type u} {predicate : α → Prop} :
    PrimitiveRule (Subtype predicate) α
      (ComplexObserver.none (Subtype predicate))
      (ComplexObserver.none α) where
  relation x y := y = x.val
  observationEq := by intros; rfl

namespace Primitive

theorem natComplex (n : ℕ) :
    @Primitive ℕ ℂ natComplexObserver complexComplexObserver inferInstance n (n : ℂ) := by
  rfl

theorem intComplex (z : ℤ) :
    @Primitive ℤ ℂ intComplexObserver complexComplexObserver inferInstance z (z : ℂ) := by
  rfl

theorem ratComplex (q : ℚ) :
    @Primitive ℚ ℂ ratComplexObserver complexComplexObserver inferInstance q (q : ℂ) := by
  rfl

theorem realComplex (r : ℝ) :
    @Primitive ℝ ℂ realComplexObserver complexComplexObserver inferInstance r (r : ℂ) := by
  rfl

theorem natComplexNoObservation (n : ℕ) :
    @Primitive ℕ ℂ
      (ComplexObserver.none ℕ) (ComplexObserver.none ℂ)
      inferInstance n (n : ℂ) := by
  rfl

theorem intComplexNoObservation (z : ℤ) :
    @Primitive ℤ ℂ
      (ComplexObserver.none ℤ) (ComplexObserver.none ℂ)
      inferInstance z (z : ℂ) := by
  rfl

theorem ratComplexNoObservation (q : ℚ) :
    @Primitive ℚ ℂ
      (ComplexObserver.none ℚ) (ComplexObserver.none ℂ)
      inferInstance q (q : ℂ) := by
  rfl

theorem realComplexNoObservation (r : ℝ) :
    @Primitive ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ)
      inferInstance r (r : ℂ) := by
  rfl

theorem subtype
    {α : Type u}
    {predicate : α → Prop}
    [observer : ComplexObserver α]
    (x : Subtype predicate) :
    @Primitive (Subtype predicate) α
      (ComplexObserver.subtype observer) observer inferInstance x x.val := by
  rfl

end Primitive

/-- Litex semantic equality. It is heterogeneous and is generated by explicit
representation bridges, reflexivity, symmetry, and transitivity. -/
inductive Same :
    {α β : Type u} →
      [_leftObserver : ComplexObserver α] →
      [_rightObserver : ComplexObserver β] →
      α → β → Prop where
  | base
      {α β : Litex.u.{u}}
      [leftObserver : ComplexObserver α]
      [rightObserver : ComplexObserver β]
      {x : α}
      {y : β}
      [rule : PrimitiveRule α β leftObserver rightObserver] :
      @Primitive α β leftObserver rightObserver rule x y → Same x y
  | derived
      {α β : Litex.u.{u}}
      [leftObserver : ComplexObserver α]
      [rightObserver : ComplexObserver β]
      {x : α}
      {y : β}
      [rule : DerivedRule α β leftObserver rightObserver] :
      @Derived α β leftObserver rightObserver rule x y → Same x y
  | refl
      {α : Litex.u.{u}}
      [observer : ComplexObserver α]
      (x : α) :
      Same x x
  | singleton
      {α : Litex.u.{u}}
      [observer : ComplexObserver α]
      (value : α) :
      @Same α (SingletonCarrier value)
        observer (ComplexObserver.singleton observer value) value
        (@SingletonCarrier.element.{u} α value : SingletonCarrier.{u} value)
  | singletonNoObservation
      {α : Litex.u.{u}}
      (value : α) :
      @Same α (SingletonCarrier value)
        (ComplexObserver.none α)
        (ComplexObserver.none (SingletonCarrier value)) value
        (@SingletonCarrier.element.{u} α value : SingletonCarrier.{u} value)
  | sumLeft
      {α β : Litex.u.{u}}
      [leftObserver : ComplexObserver α]
      [rightObserver : ComplexObserver β]
      (value : α) :
      @Same α (Sum α β)
        leftObserver (ComplexObserver.sum leftObserver rightObserver)
        value (Sum.inl value)
  | sumLeftNoObservation
      {α β : Litex.u.{u}}
      (value : α) :
      @Same α (Sum α β)
        (ComplexObserver.none α)
        (ComplexObserver.none (Sum α β))
        value (Sum.inl value)
  | sumRight
      {α β : Litex.u.{u}}
      [leftObserver : ComplexObserver α]
      [rightObserver : ComplexObserver β]
      (value : β) :
      @Same β (Sum α β)
        rightObserver (ComplexObserver.sum leftObserver rightObserver)
        value (Sum.inr value)
  | sumRightNoObservation
      {α β : Litex.u.{u}}
      (value : β) :
      @Same β (Sum α β)
        (ComplexObserver.none β)
        (ComplexObserver.none (Sum α β))
        value (Sum.inr value)
  | symm
      {α β : Litex.u.{u}}
      [leftObserver : ComplexObserver α]
      [rightObserver : ComplexObserver β]
      {x : α}
      {y : β} :
      Same x y → Same y x
  | trans
      {α β γ : Litex.u.{u}}
      [leftObserver : ComplexObserver α]
      [middleObserver : ComplexObserver β]
      [rightObserver : ComplexObserver γ]
      {x : α}
      {y : β}
      {z : γ} :
      Same x y → Same y z → Same x z
  | forgetObservation
      {α β : Litex.u.{u}}
      {leftObserver : ComplexObserver α}
      {rightObserver : ComplexObserver β}
      {x : α}
      {y : β} :
      @Same α β leftObserver rightObserver x y →
      @Same α β
        (ComplexObserver.none α)
        (ComplexObserver.none β) x y

namespace Same

/-- Every `Same` proof preserves the observers indexed by its endpoint
carriers. Numeric observers therefore turn a checked semantic-equality path
into an ordinary equality of optional complex values. -/
theorem observationEq
    {α β : Type u}
    [leftObserver : ComplexObserver α]
    [rightObserver : ComplexObserver β]
    {x : α}
    {y : β}
    (same : Same x y) :
    leftObserver.observe x = rightObserver.observe y := by
  induction same with
  | base edge => exact PrimitiveRule.observationEq edge
  | derived edge => exact DerivedRule.observationEq edge
  | refl => rfl
  | singleton => rfl
  | singletonNoObservation => rfl
  | sumLeft => rfl
  | sumLeftNoObservation => rfl
  | sumRight => rfl
  | sumRightNoObservation => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ left right => exact left.trans right
  | forgetObservation _ => rfl

/-- Discard observer metadata while preserving checked semantic equality.
This is intentionally one-way: generic membership may consume a stronger
numeric `Same`, but a no-observation proof cannot manufacture native numeric
equality. -/
theorem withoutObservation
    {α β : Type u}
    {leftObserver : ComplexObserver α}
    {rightObserver : ComplexObserver β}
    {x : α}
    {y : β}
    (same : @Same α β leftObserver rightObserver x y) :
    @Same α β
      (ComplexObserver.none α)
      (ComplexObserver.none β) x y :=
  Same.forgetObservation same

end Same

/-- The reviewed native real/complex operations whose representation
congruence is part of the compiler ABI. -/
inductive RealComplexDerived : ℝ → ℂ → Prop where
  | add
      {r s : ℝ}
      {z w : ℂ} :
      Same r z → Same s w → RealComplexDerived (r + s) (z + w)
  | sub
      {r s : ℝ}
      {z w : ℂ} :
      Same r z → Same s w → RealComplexDerived (r - s) (z - w)
  | mul
      {r s : ℝ}
      {z w : ℂ} :
      Same r z → Same s w → RealComplexDerived (r * s) (z * w)
  | div
      {r s : ℝ}
      {z w : ℂ} :
      Same r z → Same s w → RealComplexDerived (r / s) (z / w)

instance : DerivedRule ℝ ℂ realComplexObserver complexComplexObserver where
  relation := RealComplexDerived
  observationEq := by
    intro _ _ relation
    cases relation with
    | add left right =>
        apply congrArg some
        push_cast
        exact congrArg₂ (fun x y : ℂ => x + y)
          (Option.some.inj left.observationEq)
          (Option.some.inj right.observationEq)
    | sub left right =>
        apply congrArg some
        push_cast
        exact congrArg₂ (fun x y : ℂ => x - y)
          (Option.some.inj left.observationEq)
          (Option.some.inj right.observationEq)
    | mul left right =>
        apply congrArg some
        push_cast
        exact congrArg₂ (fun x y : ℂ => x * y)
          (Option.some.inj left.observationEq)
          (Option.some.inj right.observationEq)
    | div left right =>
        apply congrArg some
        push_cast
        exact congrArg₂ (fun x y : ℂ => x / y)
          (Option.some.inj left.observationEq)
          (Option.some.inj right.observationEq)

/-- The same reviewed real/complex operation edges under the deliberately
nonnumeric observer used by generic heterogeneous membership and `AsReal`. -/
inductive RealComplexNoObservationDerived : ℝ → ℂ → Prop where
  | add
      {r s : ℝ}
      {z w : ℂ} :
      @Same ℝ ℂ (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) r z →
      @Same ℝ ℂ (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) s w →
      RealComplexNoObservationDerived (r + s) (z + w)
  | sub
      {r s : ℝ}
      {z w : ℂ} :
      @Same ℝ ℂ (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) r z →
      @Same ℝ ℂ (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) s w →
      RealComplexNoObservationDerived (r - s) (z - w)
  | mul
      {r s : ℝ}
      {z w : ℂ} :
      @Same ℝ ℂ (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) r z →
      @Same ℝ ℂ (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) s w →
      RealComplexNoObservationDerived (r * s) (z * w)
  | div
      {r s : ℝ}
      {z w : ℂ} :
      @Same ℝ ℂ (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) r z →
      @Same ℝ ℂ (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) s w →
      RealComplexNoObservationDerived (r / s) (z / w)

instance :
    DerivedRule ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) where
  relation := RealComplexNoObservationDerived
  observationEq := by intros; rfl

/-- The reviewed native integer/complex operations used when a checked
integer-valued Litex function is represented directly in Lean. -/
inductive IntComplexDerived : ℤ → ℂ → Prop where
  | add
      {a b : ℤ}
      {z w : ℂ} :
      Same a z → Same b w → IntComplexDerived (a + b) (z + w)
  | sub
      {a b : ℤ}
      {z w : ℂ} :
      Same a z → Same b w → IntComplexDerived (a - b) (z - w)
  | mul
      {a b : ℤ}
      {z w : ℂ} :
      Same a z → Same b w → IntComplexDerived (a * b) (z * w)

instance : DerivedRule ℤ ℂ intComplexObserver complexComplexObserver where
  relation := IntComplexDerived
  observationEq := by
    intro _ _ relation
    cases relation with
    | add left right =>
        apply congrArg some
        push_cast
        exact congrArg₂ (fun x y : ℂ => x + y)
          (Option.some.inj left.observationEq)
          (Option.some.inj right.observationEq)
    | sub left right =>
        apply congrArg some
        push_cast
        exact congrArg₂ (fun x y : ℂ => x - y)
          (Option.some.inj left.observationEq)
          (Option.some.inj right.observationEq)
    | mul left right =>
        apply congrArg some
        push_cast
        exact congrArg₂ (fun x y : ℂ => x * y)
          (Option.some.inj left.observationEq)
          (Option.some.inj right.observationEq)

inductive IntIntAddDerived : ℤ → ℤ → Prop where
  | add
      {a b c d : ℤ} :
      Same a b → Same c d → IntIntAddDerived (a + c) (b + d)

instance : DerivedRule ℤ ℤ intComplexObserver intComplexObserver where
  relation := IntIntAddDerived
  observationEq := by
    intro _ _ relation
    cases relation with
    | add left right =>
        apply congrArg some
        push_cast
        exact congrArg₂ (fun x y : ℂ => x + y)
          (Option.some.inj left.observationEq)
          (Option.some.inj right.observationEq)

/-- Reviewed complex-target addition congruence, including the exact mixed
complex/integer source shape emitted by numeric Litex expressions. -/
inductive ComplexComplexAddDerived : ℂ → ℂ → Prop where
  | add
      {a b c d : ℂ} :
      Same a b → Same c d → ComplexComplexAddDerived (a + c) (b + d)
  | addRightInt
      {a b c : ℂ}
      {z : ℤ} :
      Same a b → Same z c →
        ComplexComplexAddDerived (a + (z : ℂ)) (b + c)

instance : DerivedRule ℂ ℂ complexComplexObserver complexComplexObserver where
  relation := ComplexComplexAddDerived
  observationEq := by
    intro _ _ relation
    cases relation with
    | add left right =>
        apply congrArg some
        exact congrArg₂ (fun x y : ℂ => x + y)
          (Option.some.inj left.observationEq)
          (Option.some.inj right.observationEq)
    | addRightInt left right =>
        apply congrArg some
        exact congrArg₂ (fun x y : ℂ => x + y)
          (Option.some.inj left.observationEq)
          (Option.some.inj right.observationEq)

namespace Same

/-- The global identity inclusion is `Lean Eq ⊆ Litex.Same`: native Lean
equality is always a valid proof of Litex semantic equality.  The converse is
not global, even when both endpoints have the same Lean type; it requires a
separate faithful/injective observation theorem such as `complexNativeEq`. -/
theorem ofEq
    {α : Litex.u.{u}}
    [observer : ComplexObserver α]
    {x y : α}
    (h : x = y) :
    Same x y := by
  subst y
  exact .refl x

theorem reflNoObservation {α : Type u} (x : α) :
    @Same α α (ComplexObserver.none α) (ComplexObserver.none α) x x :=
  @Same.refl α (ComplexObserver.none α) x

theorem ofEqNoObservation
    {α : Type u}
    {x y : α}
    (equality : x = y) :
    @Same α α (ComplexObserver.none α) (ComplexObserver.none α) x y := by
  subst y
  exact reflNoObservation x

theorem symmNoObservation
    {α β : Type u}
    {x : α}
    {y : β}
    (same : @Same α β
      (ComplexObserver.none α)
      (ComplexObserver.none β)
      x y) :
    @Same β α
      (ComplexObserver.none β)
      (ComplexObserver.none α)
      y x :=
  @Same.symm α β
    (ComplexObserver.none α) (ComplexObserver.none β)
    x y same

theorem transNoObservation
    {α β γ : Type u}
    {x : α}
    {y : β}
    {z : γ}
    (left : @Same α β
      (ComplexObserver.none α)
      (ComplexObserver.none β)
      x y)
    (right : @Same β γ
      (ComplexObserver.none β)
      (ComplexObserver.none γ)
      y z) :
    @Same α γ
      (ComplexObserver.none α)
      (ComplexObserver.none γ)
      x z :=
  @Same.trans α β γ
    (ComplexObserver.none α)
    (ComplexObserver.none β)
    (ComplexObserver.none γ)
    x y z left right

/-- Complex addition respects retained complex-carrier semantic equality. -/
theorem addCongr
    {a b c d : ℂ}
    (left : Same a b)
    (right : Same c d) :
    Same (a + c) (b + d) :=
  .derived (ComplexComplexAddDerived.add left right)

/-- A complex expression plus an integer expression may be transported to
two complex expressions using the exact integer-to-complex child proof. -/
theorem addCongrRightInt
    {a b c : ℂ}
    {z : ℤ}
    (left : Same a b)
    (right : Same z c) :
    Same (a + (z : ℂ)) (b + c) :=
  .derived (ComplexComplexAddDerived.addRightInt left right)

/-- Addition on the exact integer carrier respects retained semantic
equality on both integer operands. -/
theorem intAddCongr
    {a b c d : ℤ}
    (left : Same a b)
    (right : Same c d) :
    Same (a + c) (b + d) :=
  .derived (IntIntAddDerived.add left right)

theorem natComplex (n : ℕ) : Same n (n : ℂ) :=
  .base (Primitive.natComplex n)

theorem natComplexNoObservation (n : ℕ) :
    @Same ℕ ℂ (ComplexObserver.none ℕ) (ComplexObserver.none ℂ) n (n : ℂ) :=
  @Same.base ℕ ℂ
    (ComplexObserver.none ℕ) (ComplexObserver.none ℂ)
    n (n : ℂ) inferInstance (Primitive.natComplexNoObservation n)

theorem intComplex (z : ℤ) : Same z (z : ℂ) :=
  .base (Primitive.intComplex z)

theorem intComplexNoObservation (z : ℤ) :
    @Same ℤ ℂ (ComplexObserver.none ℤ) (ComplexObserver.none ℂ) z (z : ℂ) :=
  @Same.base ℤ ℂ
    (ComplexObserver.none ℤ) (ComplexObserver.none ℂ)
    z (z : ℂ) inferInstance (Primitive.intComplexNoObservation z)

/-- Transport an exact integer value to the particular complex expression
chosen by the checked source reduction.  The equality premise is discharged
by Lean; this theorem adds no new semantic rule beyond `intComplex`. -/
theorem intComplexOfEq
    {z : ℤ}
    {w : ℂ}
    (h : (z : ℂ) = w) :
    Same z w :=
  .trans (intComplex z) (ofEq h)

theorem ratComplex (q : ℚ) : Same q (q : ℂ) :=
  .base (Primitive.ratComplex q)

theorem ratComplexNoObservation (q : ℚ) :
    @Same ℚ ℂ (ComplexObserver.none ℚ) (ComplexObserver.none ℂ) q (q : ℂ) :=
  @Same.base ℚ ℂ
    (ComplexObserver.none ℚ) (ComplexObserver.none ℂ)
    q (q : ℂ) inferInstance (Primitive.ratComplexNoObservation q)

theorem realComplex (r : ℝ) : Same r (r : ℂ) :=
  .base (Primitive.realComplex r)

theorem realComplexNoObservation (r : ℝ) :
    @Same ℝ ℂ (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) r (r : ℂ) :=
  @Same.base ℝ ℂ
    (ComplexObserver.none ℝ) (ComplexObserver.none ℂ)
    r (r : ℂ) inferInstance (Primitive.realComplexNoObservation r)

theorem complexNat (n : ℕ) : Same (n : ℂ) n :=
  .symm (natComplex n)

theorem complexNatNoObservation (n : ℕ) :
    @Same ℂ ℕ (ComplexObserver.none ℂ) (ComplexObserver.none ℕ) (n : ℂ) n :=
  @Same.symm ℕ ℂ
    (ComplexObserver.none ℕ) (ComplexObserver.none ℂ)
    n (n : ℂ) (natComplexNoObservation n)

theorem complexInt (z : ℤ) : Same (z : ℂ) z :=
  .symm (intComplex z)

theorem complexIntNoObservation (z : ℤ) :
    @Same ℂ ℤ (ComplexObserver.none ℂ) (ComplexObserver.none ℤ) (z : ℂ) z :=
  @Same.symm ℤ ℂ
    (ComplexObserver.none ℤ) (ComplexObserver.none ℂ)
    z (z : ℂ) (intComplexNoObservation z)

theorem complexRat (q : ℚ) : Same (q : ℂ) q :=
  .symm (ratComplex q)

theorem complexRatNoObservation (q : ℚ) :
    @Same ℂ ℚ (ComplexObserver.none ℂ) (ComplexObserver.none ℚ) (q : ℂ) q :=
  @Same.symm ℚ ℂ
    (ComplexObserver.none ℚ) (ComplexObserver.none ℂ)
    q (q : ℂ) (ratComplexNoObservation q)

theorem complexReal (r : ℝ) : Same (r : ℂ) r :=
  .symm (realComplex r)

theorem complexRealNoObservation (r : ℝ) :
    @Same ℂ ℝ (ComplexObserver.none ℂ) (ComplexObserver.none ℝ) (r : ℂ) r :=
  @Same.symm ℝ ℂ
    (ComplexObserver.none ℝ) (ComplexObserver.none ℂ)
    r (r : ℂ) (realComplexNoObservation r)

theorem subtype
    {α : Type u}
    {predicate : α → Prop}
    [observer : ComplexObserver α]
    (x : Subtype predicate) :
    Same x x.val :=
  .base (Primitive.subtype x)

/-- The same subtype/value bridge under the deliberately nonnumeric observer
used by generic heterogeneous membership. -/
theorem subtypeNoObservation
    {α : Type u}
    {predicate : α → Prop}
    (x : Subtype predicate) :
    @Same (Subtype predicate) α
      (ComplexObserver.none (Subtype predicate))
      (ComplexObserver.none α)
      x x.val :=
  @Same.base (Subtype predicate) α
    (ComplexObserver.none (Subtype predicate))
    (ComplexObserver.none α)
    x x.val inferInstance (by rfl)

/-- Addition respects the closed real-to-complex representation relation. -/
theorem realAddComplex
    {r s : ℝ}
    {z w : ℂ}
    (hr : Same r z)
    (hs : Same s w) :
    Same (r + s) (z + w) :=
  .derived (RealComplexDerived.add hr hs)

/-- Subtraction respects the closed real-to-complex representation relation. -/
theorem realSubComplex
    {r s : ℝ}
    {z w : ℂ}
    (hr : Same r z)
    (hs : Same s w) :
    Same (r - s) (z - w) :=
  .derived (RealComplexDerived.sub hr hs)

/-- Multiplication respects the closed real-to-complex representation relation. -/
theorem realMulComplex
    {r s : ℝ}
    {z w : ℂ}
    (hr : Same r z)
    (hs : Same s w) :
    Same (r * s) (z * w) :=
  .derived (RealComplexDerived.mul hr hs)

/-- Division respects the closed real-to-complex representation relation.
Mathlib division is total; Litex domain clauses remain separate call
requirements and are not erased by this congruence theorem. -/
theorem realDivComplex
    {r s : ℝ}
    {z w : ℂ}
    (hr : Same r z)
    (hs : Same s w) :
    Same (r / s) (z / w) :=
  .derived (RealComplexDerived.div hr hs)

theorem realAddComplexNoObservation
    {r s : ℝ}
    {z w : ℂ}
    (hr : @Same ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) r z)
    (hs : @Same ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) s w) :
    @Same ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ)
      (r + s) (z + w) :=
  @Same.derived ℝ ℂ
    (ComplexObserver.none ℝ) (ComplexObserver.none ℂ)
    (r + s) (z + w) inferInstance
    (RealComplexNoObservationDerived.add hr hs)

theorem realSubComplexNoObservation
    {r s : ℝ}
    {z w : ℂ}
    (hr : @Same ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) r z)
    (hs : @Same ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) s w) :
    @Same ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ)
      (r - s) (z - w) :=
  @Same.derived ℝ ℂ
    (ComplexObserver.none ℝ) (ComplexObserver.none ℂ)
    (r - s) (z - w) inferInstance
    (RealComplexNoObservationDerived.sub hr hs)

theorem realMulComplexNoObservation
    {r s : ℝ}
    {z w : ℂ}
    (hr : @Same ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) r z)
    (hs : @Same ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) s w) :
    @Same ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ)
      (r * s) (z * w) :=
  @Same.derived ℝ ℂ
    (ComplexObserver.none ℝ) (ComplexObserver.none ℂ)
    (r * s) (z * w) inferInstance
    (RealComplexNoObservationDerived.mul hr hs)

theorem realDivComplexNoObservation
    {r s : ℝ}
    {z w : ℂ}
    (hr : @Same ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) r z)
    (hs : @Same ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ) s w) :
    @Same ℝ ℂ
      (ComplexObserver.none ℝ) (ComplexObserver.none ℂ)
      (r / s) (z / w) :=
  @Same.derived ℝ ℂ
    (ComplexObserver.none ℝ) (ComplexObserver.none ℂ)
    (r / s) (z / w) inferInstance
    (RealComplexNoObservationDerived.div hr hs)

theorem intAddComplex
    {a b : ℤ}
    {z w : ℂ}
    (ha : Same a z)
    (hb : Same b w) :
    Same (a + b) (z + w) :=
  .derived (IntComplexDerived.add ha hb)

/-- Congruence for the compiler's exact numeric rendering of an integer
addition: the source operands are individually embedded into `ℂ` before the
addition is formed.  This is distinct from `intAddComplex`, whose source is the
native integer sum. -/
theorem intCastAddComplex
    {a b : ℤ}
    {z w : ℂ}
    (ha : Same a z)
    (hb : Same b w) :
    Same (((a : ℤ) : ℂ) + ((b : ℤ) : ℂ)) (z + w) :=
  .trans
    (.symm (intAddComplex (intComplex a) (intComplex b)))
    (intAddComplex ha hb)

theorem intSubComplex
    {a b : ℤ}
    {z w : ℂ}
    (ha : Same a z)
    (hb : Same b w) :
    Same (a - b) (z - w) :=
  .derived (IntComplexDerived.sub ha hb)

theorem intMulComplex
    {a b : ℤ}
    {z w : ℂ}
    (ha : Same a z)
    (hb : Same b w) :
    Same (a * b) (z * w) :=
  .derived (IntComplexDerived.mul ha hb)

end Same

/-- Independent native-complex observation of one Litex carrier value.

Unlike `Litex.In`, this proposition does not use `Same`: it is the statement
that the carrier's selected observer is exactly the supplied complex value. -/
def AsComplex
    {α : Type u}
    [observer : ComplexObserver α]
    (value : α)
    (complexValue : ℂ) : Prop :=
  observer.observe value = some complexValue

/-- A value is complex-observable when it has a native `ℂ` observation. -/
def InComplex
    {α : Type u}
    [observer : ComplexObserver α]
    (value : α) : Prop :=
  ∃ complexValue : ℂ, AsComplex value complexValue

namespace InComplex

/-- The native complex value selected by one `InComplex` proof. -/
noncomputable def value
    {α : Type u}
    [observer : ComplexObserver α]
    (source : α)
    (evidence : InComplex source) : ℂ :=
  Classical.choose evidence

/-- The selected value really is the source value's complex observation. -/
theorem value_spec
    {α : Type u}
    [observer : ComplexObserver α]
    (source : α)
    (evidence : InComplex source) :
    AsComplex source (value source evidence) :=
  Classical.choose_spec evidence

end InComplex

namespace AsComplex

theorem nat (n : ℕ) : AsComplex n (n : ℂ) := by rfl
theorem int (z : ℤ) : AsComplex z (z : ℂ) := by rfl
theorem rat (q : ℚ) : AsComplex q (q : ℂ) := by rfl
theorem real (r : ℝ) : AsComplex r (r : ℂ) := by rfl
theorem complex (z : ℂ) : AsComplex z z := by rfl

/-- A fixed carrier value has at most one complex observation. -/
theorem unique
    {α : Type u}
    [observer : ComplexObserver α]
    {value : α}
    {left right : ℂ}
    (leftEvidence : AsComplex value left)
    (rightEvidence : AsComplex value right) :
    left = right := by
  exact Option.some.inj (leftEvidence.symm.trans rightEvidence)

end AsComplex

namespace Same

/-- Transport an independent complex observation along semantic equality. -/
theorem asComplex
    {α β : Type u}
    [leftObserver : ComplexObserver α]
    [rightObserver : ComplexObserver β]
    {left : α}
    {right : β}
    {value : ℂ}
    (same : Same left right)
    (leftEvidence : AsComplex left value) :
    AsComplex right value := by
  exact same.observationEq.symm.trans leftEvidence

/-- `Same` preserves and reflects independent complex observability. -/
theorem inComplexIff
    {α β : Type u}
    [leftObserver : ComplexObserver α]
    [rightObserver : ComplexObserver β]
    {left : α}
    {right : β}
    (same : Same left right) :
    InComplex left ↔ InComplex right := by
  constructor
  · rintro ⟨value, evidence⟩
    exact ⟨value, same.asComplex evidence⟩
  · rintro ⟨value, evidence⟩
    exact ⟨value, same.symm.asComplex evidence⟩

/-- `Same` plus complex observations yields Lean's native equality between
the two observed `ℂ` values. -/
theorem complexEq
    {α β : Type u}
    [leftObserver : ComplexObserver α]
    [rightObserver : ComplexObserver β]
    {left : α}
    {right : β}
    {leftValue rightValue : ℂ}
    (same : Same left right)
    (leftEvidence : AsComplex left leftValue)
    (rightEvidence : AsComplex right rightValue) :
    leftValue = rightValue := by
  exact AsComplex.unique (same.asComplex leftEvidence) rightEvidence

/-- The direct public contract requested by numeric consumers: `Same` plus
`InComplex` evidence on both endpoints makes their selected native complex
values equal. -/
theorem inComplexEq
    {α β : Type u}
    [leftObserver : ComplexObserver α]
    [rightObserver : ComplexObserver β]
    {left : α}
    {right : β}
    (same : Same left right)
    (leftEvidence : InComplex left)
    (rightEvidence : InComplex right) :
    InComplex.value left leftEvidence =
      InComplex.value right rightEvidence :=
  same.complexEq
    (InComplex.value_spec left leftEvidence)
    (InComplex.value_spec right rightEvidence)

theorem intComplexEq
    {left : ℤ}
    {right : ℂ}
    (same : Same left right) :
    (left : ℂ) = right :=
  same.complexEq (AsComplex.int left) (AsComplex.complex right)

theorem natEq {left right : ℕ} (same : Same left right) : left = right := by
  have := same.complexEq (AsComplex.nat left) (AsComplex.nat right)
  exact_mod_cast this

theorem intEq {left right : ℤ} (same : Same left right) : left = right := by
  have := same.complexEq (AsComplex.int left) (AsComplex.int right)
  exact_mod_cast this

theorem ratEq {left right : ℚ} (same : Same left right) : left = right := by
  have := same.complexEq (AsComplex.rat left) (AsComplex.rat right)
  exact_mod_cast this

theorem realEq {left right : ℝ} (same : Same left right) : left = right := by
  have := same.complexEq (AsComplex.real left) (AsComplex.real right)
  exact_mod_cast this

theorem complexNativeEq {left right : ℂ} (same : Same left right) : left = right :=
  same.complexEq (AsComplex.complex left) (AsComplex.complex right)

end Same

/-- A Litex set is represented by its exact element carrier. The carrier is
the set extension itself; no target-type-specific observation is stored. -/
structure Set where
  Carrier : Litex.u.{u}

namespace Set

/-- Package an exact Lean carrier as a Litex set. -/
abbrev ofType (α : Litex.u.{u}) : Litex.Set.{u} :=
  ⟨α⟩

/-- A Litex set is nonempty exactly when its exact carrier is inhabited. -/
def Nonempty (set : Litex.Set.{u}) : Prop :=
  _root_.Nonempty set.Carrier

/-- Finiteness is a property of the exact carrier, not a second cardinality
tag attached to a source set value. -/
def Finite (set : Litex.Set.{u}) : Prop :=
  _root_.Finite set.Carrier

/-- Empty finite Litex set carrier. -/
def empty : Litex.Set :=
  ofType PEmpty

/-- Exact singleton set carrier indexed by its sole source value. -/
def singleton {α : Type u} (value : α) : Litex.Set.{u} :=
  ofType (SingletonCarrier.{u} value)

/-- Exact finite coproduct of two Litex set carriers. This is used instead of
a universal boxed value for heterogeneous finite set literals. -/
def coproduct (left right : Litex.Set.{u}) : Litex.Set.{u} :=
  ofType (Sum left.Carrier right.Carrier)

theorem empty_finite : Finite empty := by
  unfold Finite empty
  infer_instance

theorem singleton_finite {α : Type u} (value : α) : Finite (singleton value) := by
  unfold Finite singleton
  apply _root_.Finite.of_surjective
    (fun _ : PUnit =>
      (@SingletonCarrier.element.{u} α value : SingletonCarrier.{u} value))
  intro singletonValue
  cases singletonValue
  exact ⟨PUnit.unit, rfl⟩

theorem coproduct_finite
    (left right : Litex.Set.{u})
    (hleft : Finite left)
    (hright : Finite right) :
    Finite (coproduct left right) := by
  unfold Finite coproduct at *
  letI : _root_.Finite left.Carrier := hleft
  letI : _root_.Finite right.Carrier := hright
  infer_instance

end Set

/-- Heterogeneous membership: `x` belongs to `set` when it is semantically the
same as one value in the set's exact carrier. -/
def In
    {α : Litex.u.{u}}
    (x : α)
    (set : Litex.Set.{u}) : Prop :=
  ∃ y : set.Carrier, Same.{u} x y

namespace In

/-- Every value of a set's own carrier belongs to that set automatically. -/
theorem own (set : Litex.Set.{u}) (x : set.Carrier) : In x set :=
  ⟨x, .refl x⟩

/-- Membership is invariant under Litex semantic equality. -/
theorem congr
    {α β : Litex.u.{u}}
    {x : α}
    {y : β}
    {leftObserver : ComplexObserver α}
    {rightObserver : ComplexObserver β}
    (h : @Same α β leftObserver rightObserver x y)
    (set : Litex.Set.{u}) :
    In x set ↔ In y set := by
  have hWithoutObservation := Same.withoutObservation h
  constructor
  · rintro ⟨z, hxz⟩
    exact ⟨z,
      Same.transNoObservation
        (Same.symmNoObservation hWithoutObservation) hxz⟩
  · rintro ⟨z, hyz⟩
    exact ⟨z, Same.transNoObservation hWithoutObservation hyz⟩

/-- Select the exact-carrier representative certified by a Litex membership
proof. An input already living in the set's exact carrier is its own canonical
representative; genuinely heterogeneous inputs use Lean's ordinary classical
choice. -/
noncomputable def rep
    {set : Litex.Set.{u}}
    {α : Litex.u.{u}}
    (x : α)
    (hx : In x set) :
    set.Carrier := by
  classical
  exact if h : α = set.Carrier then _root_.cast h x else Classical.choose hx

/-- Exact-carrier inputs survive representative selection definitionally.
This is the native-consumer bridge for values such as `n : ℕ` in `N`. -/
@[simp] theorem rep_exact
    {set : Litex.Set.{u}}
    (x : set.Carrier)
    (hx : In x set) :
    rep x hx = x := by
  simp [rep]

/-- The representative selected by `rep` remains semantically equal to the
source value. -/
theorem same_rep
    {set : Litex.Set.{u}}
    {α : Litex.u.{u}}
    (x : α)
    (hx : In x set) :
    Same x (rep x hx) :=
  by
    classical
    unfold rep
    split
    · rename_i h
      subst α
      exact Same.refl x
    · exact Classical.choose_spec hx

end In

/-- Exact binary union carrier. The two sides remain separately typed and are
joined only by the reviewed `Sum` representation bridges in `Same`. -/
def union (left right : Litex.Set.{u}) : Litex.Set.{u} :=
  Set.coproduct left right

/-- Exact binary intersection carrier: one representative from the left side
together with independently checked membership in the right side. -/
def intersect (left right : Litex.Set.{u}) : Litex.Set.{u} :=
  Set.ofType {value : left.Carrier // In value right}

/-- Exact set-difference carrier: one representative from the left side with
a proof that it is absent from the right side. -/
def setMinus (left right : Litex.Set.{u}) : Litex.Set.{u} :=
  Set.ofType {value : left.Carrier // ¬ In value right}

/-- Extension inclusion between two exact Litex set carriers. The element
carrier remains heterogeneous; a subset proof transports `In` evidence and
does not retype the source value. -/
def Subset (left right : Litex.Set.{u}) : Prop :=
  ∀ {alpha : Litex.u.{u}} (x : alpha), In x left → In x right

namespace Subset

/-- Select the target-carrier representative supplied by one checked subset
transport. This is uniform in both sets; numeric sets, function sets, refined
sets, and user-defined sets all use the same operation. -/
noncomputable def rep
    {left right : Litex.Set.{u}}
    (subset : Litex.Subset left right)
    {α : Litex.u.{u}}
    (value : α)
    (valueInLeft : Litex.In value left) :
    right.Carrier :=
  Litex.In.rep value (subset value valueInLeft)

/-- The target representative selected by `Subset.rep` is semantically the
same value as its source. -/
theorem same_rep
    {left right : Litex.Set.{u}}
    (subset : Litex.Subset left right)
    {α : Litex.u.{u}}
    (value : α)
    (valueInLeft : Litex.In value left) :
    Litex.Same value (rep subset value valueInLeft) :=
  Litex.In.same_rep value (subset value valueInLeft)

/-- If the source value already has the target carrier, generic subset
transport preserves it definitionally. -/
@[simp] theorem rep_exact
    {left right : Litex.Set.{u}}
    (subset : Litex.Subset left right)
    (value : right.Carrier)
    (valueInLeft : Litex.In value left) :
    rep subset value valueInLeft = value :=
  Litex.In.rep_exact value (subset value valueInLeft)

end Subset

namespace Set

/-- Evidence that every value in one exact set carrier has a reviewed
semantic representation as a complex value. This is the bridge required
when a Litex `forall x S` Result was checked with a complex source binder but
is consumed as the heterogeneous `Subset S T` contract. -/
def EveryCarrierValueHasComplexRepresentative (set : Litex.Set) : Prop :=
  ∀ value : set.Carrier,
    ∃ complexValue : ℂ,
      @Same set.Carrier ℂ
        (ComplexObserver.none set.Carrier)
        (ComplexObserver.none ℂ)
        value complexValue

theorem emptyEveryCarrierValueHasComplexRepresentative :
    EveryCarrierValueHasComplexRepresentative empty := by
  intro value
  exact PEmpty.elim value

theorem singletonEveryCarrierValueHasComplexRepresentative
    (value : ℂ) :
    EveryCarrierValueHasComplexRepresentative (singleton value) := by
  intro singletonValue
  cases singletonValue
  exact ⟨value,
    Same.symmNoObservation (Same.singletonNoObservation value)⟩

theorem coproductEveryCarrierValueHasComplexRepresentative
    {left right : Litex.Set}
    (leftEvidence : EveryCarrierValueHasComplexRepresentative left)
    (rightEvidence : EveryCarrierValueHasComplexRepresentative right) :
    EveryCarrierValueHasComplexRepresentative (coproduct left right) := by
  intro value
  cases value with
  | inl leftValue =>
      rcases leftEvidence leftValue with ⟨complexValue, representation⟩
      exact ⟨complexValue,
        Same.transNoObservation
          (Same.symmNoObservation (Same.sumLeftNoObservation leftValue))
          representation⟩
  | inr rightValue =>
      rcases rightEvidence rightValue with ⟨complexValue, representation⟩
      exact ⟨complexValue,
        Same.transNoObservation
          (Same.symmNoObservation (Same.sumRightNoObservation rightValue))
          representation⟩

/-- Turn a complex-binder membership implication retained by a recursive
statement Result into the fully heterogeneous subset contract. The source
carrier evidence is explicit; no universal boxing or unreviewed cast is used.
-/
theorem subsetFromComplexMembershipImplication
    {left right : Litex.Set}
    (leftEvidence : EveryCarrierValueHasComplexRepresentative left)
    (implication : ∀ value : ℂ, In value left → In value right) :
    Subset left right := by
  intro alpha value membership
  rcases membership with ⟨leftValue, valueToLeftValue⟩
  rcases leftEvidence leftValue with ⟨complexValue, leftValueToComplexValue⟩
  have complexMembershipInLeft : In complexValue left :=
    ⟨leftValue, Same.symmNoObservation leftValueToComplexValue⟩
  rcases implication complexValue complexMembershipInLeft with
    ⟨rightValue, complexValueToRightValue⟩
  exact ⟨rightValue,
    Same.transNoObservation valueToLeftValue
      (Same.transNoObservation
        leftValueToComplexValue complexValueToRightValue)⟩

end Set

/-- A power-set member is represented by its exact membership predicate on
the base carrier. Unlike a carrier of arbitrary `Litex.Set` syntax values,
this representation remains finite when the base carrier is finite. -/
abbrev PowerSubset (base : Litex.Set.{u}) : Type (u + 1) :=
  ULift.{u + 1, u} (base.Carrier → Prop)

def powerSubsetSet
    (base : Litex.Set.{u})
    (predicate : PowerSubset base) : Litex.Set.{u} :=
  Set.ofType {value : base.Carrier // predicate.down value}

def powerSubsetOfSet
    (base subset : Litex.Set.{u}) : PowerSubset base :=
  ULift.up (fun value : base.Carrier => In value subset)

def emptyPowerSubset (base : Litex.Set.{u}) : PowerSubset base :=
  ULift.up (fun _ : base.Carrier => False)

/-- A source set and a native power-subset predicate represent the same
mathematical set exactly when their Litex membership extensions agree. -/
instance (base : Litex.Set.{u}) :
    DerivedRule (Litex.Set.{u}) (PowerSubset base)
      (ComplexObserver.none (Litex.Set.{u}))
      (ComplexObserver.none (PowerSubset base)) where
  relation source predicate :=
    Subset source (powerSubsetSet base predicate) ∧
      Subset (powerSubsetSet base predicate) source
  observationEq := by intros; rfl

/-- Exact power-set carrier. -/
def powerSet (base : Litex.Set.{u}) : Litex.Set.{u + 1} :=
  Set.ofType (PowerSubset base)

/-- The built-in extensional set/set derived representation edge. -/
instance :
    DerivedRule (Litex.Set.{u}) (Litex.Set.{u})
      (ComplexObserver.none (Litex.Set.{u}))
      (ComplexObserver.none (Litex.Set.{u})) where
  relation left right := Subset left right ∧ Subset right left
  observationEq := by intros; rfl

namespace Same

theorem setExt
    {left right : Litex.Set.{u}}
    (forward : Subset left right)
    (backward : Subset right left) :
    Same left right := by
  apply Same.derived
  change Subset left right ∧ Subset right left
  exact ⟨forward, backward⟩

end Same

namespace SetRules

theorem inUnionLeft
    {left right : Litex.Set.{u}}
    {alpha : Type u}
    {value : alpha}
    (membership : In value left) :
    In value (union left right) := by
  rcases membership with ⟨representative, same⟩
  exact ⟨Sum.inl representative,
    Same.trans same (Same.sumLeftNoObservation representative)⟩

theorem inUnionRight
    {left right : Litex.Set.{u}}
    {alpha : Type u}
    {value : alpha}
    (membership : In value right) :
    In value (union left right) := by
  rcases membership with ⟨representative, same⟩
  exact ⟨Sum.inr representative,
    Same.trans same (Same.sumRightNoObservation representative)⟩

theorem unionCases
    {left right : Litex.Set.{u}}
    {alpha : Type u}
    {value : alpha}
    (membership : In value (union left right)) :
    In value left ∨ In value right := by
  rcases membership with ⟨representative, same⟩
  cases representative with
  | inl leftValue =>
      exact Or.inl ⟨leftValue,
        Same.trans same (Same.symm (Same.sumLeftNoObservation leftValue))⟩
  | inr rightValue =>
      exact Or.inr ⟨rightValue,
        Same.trans same (Same.symm (Same.sumRightNoObservation rightValue))⟩

theorem inIntersect
    {left right : Litex.Set.{u}}
    {alpha : Type u}
    {value : alpha}
    (leftMembership : In value left)
    (rightMembership : In value right) :
    In value (intersect left right) := by
  let representative := In.rep value leftMembership
  have sameRepresentative : Same value representative := In.same_rep value leftMembership
  have representativeInRight : In representative right :=
    (In.congr sameRepresentative right).mp rightMembership
  let exactValue : {value : left.Carrier // In value right} :=
    ⟨representative, representativeInRight⟩
  exact ⟨exactValue, Same.trans sameRepresentative (Same.symm (Same.subtypeNoObservation exactValue))⟩

theorem inLeftOfInIntersect
    {left right : Litex.Set.{u}}
    {alpha : Type u}
    {value : alpha}
    (membership : In value (intersect left right)) :
    In value left := by
  rcases membership with ⟨representative, same⟩
  exact ⟨representative.val, Same.trans same (Same.subtypeNoObservation representative)⟩

theorem inRightOfInIntersect
    {left right : Litex.Set.{u}}
    {alpha : Type u}
    {value : alpha}
    (membership : In value (intersect left right)) :
    In value right := by
  rcases membership with ⟨representative, same⟩
  have sameValue : Same value representative.val :=
    Same.trans same (Same.subtypeNoObservation representative)
  exact (In.congr sameValue right).mpr representative.property

theorem notInIntersectOfNotInLeft
    {left right : Litex.Set.{u}}
    {alpha : Type u}
    {value : alpha}
    (notMember : ¬ In value left) :
    ¬ In value (intersect left right) :=
  fun member => notMember (inLeftOfInIntersect member)

theorem notInIntersectOfNotInRight
    {left right : Litex.Set.{u}}
    {alpha : Type u}
    {value : alpha}
    (notMember : ¬ In value right) :
    ¬ In value (intersect left right) :=
  fun member => notMember (inRightOfInIntersect member)

theorem inSetMinus
    {left right : Litex.Set.{u}}
    {alpha : Type u}
    {value : alpha}
    (leftMembership : In value left)
    (rightNonmembership : ¬ In value right) :
    In value (setMinus left right) := by
  let representative := In.rep value leftMembership
  have sameRepresentative : Same value representative := In.same_rep value leftMembership
  have representativeNotInRight : ¬ In representative right := by
    intro member
    exact rightNonmembership ((In.congr sameRepresentative right).mpr member)
  let exactValue : {value : left.Carrier // ¬ In value right} :=
    ⟨representative, representativeNotInRight⟩
  exact ⟨exactValue, Same.trans sameRepresentative (Same.symm (Same.subtypeNoObservation exactValue))⟩

theorem inLeftOfInSetMinus
    {left right : Litex.Set.{u}}
    {alpha : Type u}
    {value : alpha}
    (membership : In value (setMinus left right)) :
    In value left := by
  rcases membership with ⟨representative, same⟩
  exact ⟨representative.val, Same.trans same (Same.subtypeNoObservation representative)⟩

theorem notInRightOfInSetMinus
    {left right : Litex.Set.{u}}
    {alpha : Type u}
    {value : alpha}
    (membership : In value (setMinus left right)) :
    ¬ In value right := by
  rcases membership with ⟨representative, same⟩
  have sameValue : Same value representative.val :=
    Same.trans same (Same.subtypeNoObservation representative)
  intro rightMembership
  exact representative.property ((In.congr sameValue right).mp rightMembership)

theorem emptySubset (set : Litex.Set.{u}) : Subset Set.empty set := by
  intro _ value membership
  rcases membership with ⟨impossible, _⟩
  exact PEmpty.elim impossible

theorem subsetUnionLeft (left right : Litex.Set.{u}) :
    Subset left (union left right) :=
  fun _ membership => inUnionLeft membership

theorem subsetUnionRight (left right : Litex.Set.{u}) :
    Subset right (union left right) :=
  fun _ membership => inUnionRight membership

theorem unionSubset
    {left right target : Litex.Set.{u}}
    (leftSubset : Subset left target)
    (rightSubset : Subset right target) :
    Subset (union left right) target := by
  intro _ value membership
  rcases unionCases membership with leftMembership | rightMembership
  · exact leftSubset value leftMembership
  · exact rightSubset value rightMembership

theorem intersectSubsetLeft (left right : Litex.Set.{u}) :
    Subset (intersect left right) left :=
  fun _ membership => inLeftOfInIntersect membership

theorem intersectSubsetRight (left right : Litex.Set.{u}) :
    Subset (intersect left right) right :=
  fun _ membership => inRightOfInIntersect membership

theorem setMinusSubsetLeft (left right : Litex.Set.{u}) :
    Subset (setMinus left right) left :=
  fun _ membership => inLeftOfInSetMinus membership

theorem unionFinite
    (left right : Litex.Set.{u})
    (leftFinite : Set.Finite left)
    (rightFinite : Set.Finite right) :
    Set.Finite (union left right) :=
  Set.coproduct_finite left right leftFinite rightFinite

theorem intersectFinite
    (left right : Litex.Set.{u})
    (leftFinite : Set.Finite left) :
    Set.Finite (intersect left right) := by
  unfold Set.Finite intersect at *
  letI : _root_.Finite left.Carrier := leftFinite
  infer_instance

theorem setMinusFiniteLeft
    (left right : Litex.Set.{u})
    (leftFinite : Set.Finite left) :
    Set.Finite (setMinus left right) := by
  unfold Set.Finite setMinus at *
  letI : _root_.Finite left.Carrier := leftFinite
  infer_instance

theorem unionNonemptyLeft
    (left right : Litex.Set.{u})
    (leftNonempty : Set.Nonempty left) :
    Set.Nonempty (union left right) := by
  rcases leftNonempty with ⟨value⟩
  exact ⟨Sum.inl value⟩

theorem unionNonemptyRight
    (left right : Litex.Set.{u})
    (rightNonempty : Set.Nonempty right) :
    Set.Nonempty (union left right) := by
  rcases rightNonempty with ⟨value⟩
  exact ⟨Sum.inr value⟩

theorem subsetSamePowerMember
    {subset base : Litex.Set.{u}}
    (subsetBase : Subset subset base) :
    Same subset (powerSubsetOfSet base subset) := by
  apply Same.derived
  change
    Subset subset
        (powerSubsetSet base (powerSubsetOfSet base subset)) ∧
      Subset
        (powerSubsetSet base (powerSubsetOfSet base subset)) subset
  constructor
  · intro _ value membership
    rcases subsetBase value membership with ⟨baseValue, sameBase⟩
    have baseValueMembership : In baseValue subset :=
      (In.congr sameBase subset).mp membership
    let exactValue : {value : base.Carrier // In value subset} :=
      ⟨baseValue, baseValueMembership⟩
    exact
      ⟨exactValue, Same.trans sameBase (Same.symm (Same.subtypeNoObservation exactValue))⟩
  · intro _ value membership
    rcases membership with ⟨exactValue, sameExact⟩
    have sameValue : Same value exactValue.val :=
      Same.trans sameExact (Same.subtypeNoObservation exactValue)
    exact (In.congr sameValue subset).mpr exactValue.property

theorem inPowerSetOfSubset
    {subset base : Litex.Set.{u}}
    (subsetBase : Subset subset base) :
    In subset (powerSet base) :=
  ⟨powerSubsetOfSet base subset,
    subsetSamePowerMember subsetBase⟩

theorem powerSetNonempty (base : Litex.Set.{u}) :
    Set.Nonempty (powerSet base) :=
  ⟨emptyPowerSubset base⟩

theorem powerSetFinite
    (base : Litex.Set.{u})
    (baseFinite : Set.Finite base) :
    Set.Finite (powerSet base) := by
  unfold Set.Finite powerSet
  letI : _root_.Finite base.Carrier := baseFinite
  infer_instance

theorem unionCommutative (left right : Litex.Set.{u}) :
    Same (union left right) (union right left) :=
  Same.setExt
    (fun value membership => by
      rcases unionCases membership with leftMember | rightMember
      · exact inUnionRight leftMember
      · exact inUnionLeft rightMember)
    (fun value membership => by
      rcases unionCases membership with rightMember | leftMember
      · exact inUnionRight rightMember
      · exact inUnionLeft leftMember)

theorem unionAssociative (left middle right : Litex.Set.{u}) :
    Same (union (union left middle) right) (union left (union middle right)) :=
  Same.setExt
    (fun value membership => by
      rcases unionCases membership with leftMiddle | rightMember
      · rcases unionCases leftMiddle with leftMember | middleMember
        · exact inUnionLeft leftMember
        · exact inUnionRight (inUnionLeft middleMember)
      · exact inUnionRight (inUnionRight rightMember))
    (fun value membership => by
      rcases unionCases membership with leftMember | middleRight
      · exact inUnionLeft (inUnionLeft leftMember)
      · rcases unionCases middleRight with middleMember | rightMember
        · exact inUnionLeft (inUnionRight middleMember)
        · exact inUnionRight rightMember)

theorem unionIdempotent (set : Litex.Set.{u}) : Same (union set set) set :=
  Same.setExt
    (fun _ membership => (unionCases membership).elim id id)
    (fun _ membership => inUnionLeft membership)

theorem unionEmptyRight (set : Litex.Set.{u}) : Same (union set Set.empty) set :=
  Same.setExt
    (fun _ membership => by
      rcases unionCases membership with member | impossible
      · exact member
      · rcases impossible with ⟨empty, _⟩
        exact PEmpty.elim empty)
    (fun _ membership => inUnionLeft membership)

theorem unionEmptyLeft (set : Litex.Set.{u}) : Same (union Set.empty set) set :=
  Same.trans (unionCommutative Set.empty set) (unionEmptyRight set)

theorem intersectCommutative (left right : Litex.Set.{u}) :
    Same (intersect left right) (intersect right left) :=
  Same.setExt
    (fun _ membership =>
      inIntersect (inRightOfInIntersect membership) (inLeftOfInIntersect membership))
    (fun _ membership =>
      inIntersect (inRightOfInIntersect membership) (inLeftOfInIntersect membership))

theorem intersectAssociative (left middle right : Litex.Set.{u}) :
    Same (intersect (intersect left middle) right)
      (intersect left (intersect middle right)) :=
  Same.setExt
    (fun _ membership =>
      inIntersect
        (inLeftOfInIntersect (inLeftOfInIntersect membership))
        (inIntersect
          (inRightOfInIntersect (inLeftOfInIntersect membership))
          (inRightOfInIntersect membership)))
    (fun _ membership =>
      inIntersect
        (inIntersect
          (inLeftOfInIntersect membership)
          (inLeftOfInIntersect (inRightOfInIntersect membership)))
        (inRightOfInIntersect (inRightOfInIntersect membership)))

theorem intersectIdempotent (set : Litex.Set.{u}) :
    Same (intersect set set) set :=
  Same.setExt
    (intersectSubsetLeft set set)
    (fun _ membership => inIntersect membership membership)

theorem subsetTransitive
    {left middle right : Litex.Set.{u}}
    (leftMiddle : Subset left middle)
    (middleRight : Subset middle right) :
    Subset left right :=
  fun value membership => middleRight value (leftMiddle value membership)

theorem intersectEqLeftOfSubset
    {left right : Litex.Set.{u}}
    (leftSubset : Subset left right) :
    Same (intersect left right) left :=
  Same.setExt
    (intersectSubsetLeft left right)
    (fun value membership => inIntersect membership (leftSubset value membership))

theorem intersectEqRightOfSubset
    {left right : Litex.Set.{u}}
    (rightSubset : Subset right left) :
    Same (intersect left right) right :=
  Same.setExt
    (intersectSubsetRight left right)
    (fun value membership => inIntersect (rightSubset value membership) membership)

theorem unionEqRightOfSubset
    {subset base : Litex.Set.{u}}
    (subsetBase : Subset subset base) :
    Same (union subset base) base :=
  Same.setExt
    (unionSubset subsetBase (fun _ membership => membership))
    (subsetUnionRight subset base)

theorem unionEqLeftOfSubset
    {subset base : Litex.Set.{u}}
    (subsetBase : Subset subset base) :
    Same (union base subset) base :=
  Same.trans
    (unionCommutative base subset)
    (unionEqRightOfSubset subsetBase)

theorem setMinusSelfEmpty (set : Litex.Set.{u}) :
    Same (setMinus set set) Set.empty :=
  Same.setExt
    (fun _ membership =>
      False.elim
        ((notInRightOfInSetMinus membership)
          (inLeftOfInSetMinus membership)))
    (emptySubset (setMinus set set))

theorem setMinusEmptyRight (set : Litex.Set.{u}) :
    Same (setMinus set Set.empty) set :=
  Same.setExt
    (setMinusSubsetLeft set Set.empty)
    (fun _ membership =>
      inSetMinus membership (fun emptyMembership => by
        rcases emptyMembership with ⟨impossible, _⟩
        exact PEmpty.elim impossible))

theorem setMinusEmptyLeft (set : Litex.Set.{u}) :
    Same (setMinus Set.empty set) Set.empty :=
  Same.setExt
    (setMinusSubsetLeft Set.empty set)
    (emptySubset (setMinus Set.empty set))

theorem intersectSetMinusOfSubsetEmpty
    (outside : Litex.Set.{u})
    {subset removed : Litex.Set.{u}}
    (subsetRemoved : Subset subset removed) :
    Same (intersect subset (setMinus outside removed)) Set.empty :=
  Same.setExt
    (fun _ membership =>
      False.elim
        ((notInRightOfInSetMinus (inRightOfInIntersect membership))
          (subsetRemoved _ (inLeftOfInIntersect membership))))
    (emptySubset (intersect subset (setMinus outside removed)))

theorem intersectSetMinusSelfEmpty (removed outside : Litex.Set.{u}) :
    Same (intersect removed (setMinus outside removed)) Set.empty :=
  intersectSetMinusOfSubsetEmpty outside (fun _ membership => membership)

theorem unionSetMinusDecomposition (retained base : Litex.Set.{u}) :
    Same (union retained (setMinus base retained)) (union retained base) :=
  Same.setExt
    (fun _ membership => by
      rcases unionCases membership with retainedMembership | differenceMembership
      · exact inUnionLeft retainedMembership
      · exact inUnionRight (inLeftOfInSetMinus differenceMembership))
    (fun value membership => by
      rcases unionCases membership with retainedMembership | baseMembership
      · exact inUnionLeft retainedMembership
      · classical
        by_cases retainedMembership : In value retained
        · exact inUnionLeft retainedMembership
        · exact inUnionRight (inSetMinus baseMembership retainedMembership))

theorem setMinusIntersectSelf (base removed : Litex.Set.{u}) :
    Same (setMinus base (intersect removed base)) (setMinus base removed) :=
  Same.setExt
    (fun _ membership =>
      inSetMinus
        (inLeftOfInSetMinus membership)
        (fun removedMembership =>
          (notInRightOfInSetMinus membership)
            (inIntersect removedMembership (inLeftOfInSetMinus membership))))
    (fun _ membership =>
      inSetMinus
        (inLeftOfInSetMinus membership)
        (fun intersectionMembership =>
          (notInRightOfInSetMinus membership)
            (inLeftOfInIntersect intersectionMembership)))

theorem setMinusIntersectSelfCommuted (base removed : Litex.Set.{u}) :
    Same (setMinus base (intersect base removed)) (setMinus base removed) :=
  Same.setExt
    (fun _ membership =>
      inSetMinus
        (inLeftOfInSetMinus membership)
        (fun removedMembership =>
          (notInRightOfInSetMinus membership)
            (inIntersect (inLeftOfInSetMinus membership) removedMembership)))
    (fun _ membership =>
      inSetMinus
        (inLeftOfInSetMinus membership)
        (fun intersectionMembership =>
          (notInRightOfInSetMinus membership)
            (inRightOfInIntersect intersectionMembership)))

theorem intersectUnionDistributive (left middle right : Litex.Set.{u}) :
    Same (intersect left (union middle right))
      (union (intersect left middle) (intersect left right)) :=
  Same.setExt
    (fun value membership => by
      have leftMembership := inLeftOfInIntersect membership
      rcases unionCases (inRightOfInIntersect membership) with middleMembership | rightMembership
      · exact inUnionLeft (inIntersect leftMembership middleMembership)
      · exact inUnionRight (inIntersect leftMembership rightMembership))
    (fun value membership => by
      rcases unionCases membership with middleMembership | rightMembership
      · exact inIntersect
          (inLeftOfInIntersect middleMembership)
          (inUnionLeft (inRightOfInIntersect middleMembership))
      · exact inIntersect
          (inLeftOfInIntersect rightMembership)
          (inUnionRight (inRightOfInIntersect rightMembership)))

theorem setMinusIntersectDeMorgan (left middle right : Litex.Set.{u}) :
    Same (setMinus left (intersect middle right))
      (union (setMinus left middle) (setMinus left right)) :=
  Same.setExt
    (fun value membership => by
      have leftMembership := inLeftOfInSetMinus membership
      have notIntersection := notInRightOfInSetMinus membership
      classical
      by_cases middleMembership : In value middle
      · exact inUnionRight (inSetMinus leftMembership (fun rightMembership =>
          notIntersection (inIntersect middleMembership rightMembership)))
      · exact inUnionLeft (inSetMinus leftMembership middleMembership))
    (fun value membership => by
      rcases unionCases membership with notMiddle | notRight
      · exact inSetMinus
          (inLeftOfInSetMinus notMiddle)
          (notInIntersectOfNotInLeft (notInRightOfInSetMinus notMiddle))
      · exact inSetMinus
          (inLeftOfInSetMinus notRight)
          (notInIntersectOfNotInRight (notInRightOfInSetMinus notRight)))

theorem setMinusUnionDeMorgan (left middle right : Litex.Set.{u}) :
    Same (setMinus left (union middle right))
      (intersect (setMinus left middle) (setMinus left right)) :=
  Same.setExt
    (fun value membership => by
      have leftMembership := inLeftOfInSetMinus membership
      have notUnion := notInRightOfInSetMinus membership
      exact inIntersect
        (inSetMinus leftMembership (fun middleMembership =>
          notUnion (inUnionLeft middleMembership)))
        (inSetMinus leftMembership (fun rightMembership =>
          notUnion (inUnionRight rightMembership))))
    (fun value membership =>
      inSetMinus
        (inLeftOfInSetMinus (inLeftOfInIntersect membership))
        (fun unionMembership => by
          rcases unionCases unionMembership with middleMembership | rightMembership
          · exact (notInRightOfInSetMinus (inLeftOfInIntersect membership)) middleMembership
          · exact (notInRightOfInSetMinus (inRightOfInIntersect membership)) rightMembership))

theorem setMinusRecoverSubset
    {left subset : Litex.Set.{u}}
    (subsetLeft : Subset subset left) :
    Same (setMinus left (setMinus left subset)) subset :=
  Same.setExt
    (fun value membership => by
      have leftMembership := inLeftOfInSetMinus membership
      have notDifference := notInRightOfInSetMinus membership
      classical
      by_contra notSubset
      exact notDifference (inSetMinus leftMembership notSubset))
    (fun value membership =>
      inSetMinus
        (subsetLeft value membership)
        (fun differenceMembership =>
          (notInRightOfInSetMinus differenceMembership) membership))

end SetRules

/-- The first compiler function carrier: one named unary Litex application
layer. Its argument remains heterogeneous; the function can be called only
with an explicit proof that the argument belongs to `domain`. -/
structure Fn
    (domain : Litex.Set.{u})
    (codomain : Litex.Set.{v}) where
  call : {α : Litex.u.{u}} → (x : α) → In x domain → codomain.Carrier
  /-- Exact-carrier application avoids `In.rep` when the caller already owns
  a value of the declared domain carrier. -/
  callOwn : domain.Carrier → codomain.Carrier :=
    fun x => call x (In.own domain x)

/-- A unary Litex function with source-domain clauses. Applicability remains
propositional: a call needs both membership in `domain` and the exact
source predicate instantiated at the argument. -/
structure FnWhere
    (domain : Litex.Set.{u})
    (codomain : Litex.Set.{v})
    (requires : {α : Litex.u.{u}} → (x : α) → In x domain → Prop) where
  call :
    {α : Litex.u.{u}} →
    (x : α) →
    (hx : In x domain) →
    requires x hx →
    codomain.Carrier

/-- The Litex set of unary functions from `domain` to `codomain`.

`Fn domain codomain` lives in `max (u + 1) v`: its `call` field accepts values
from any carrier in the domain universe and returns the exact codomain
carrier. This permits a base-universe function to return another function
set without collapsing either source application layer. -/
abbrev fnSet
    (domain : Litex.Set.{u})
    (codomain : Litex.Set.{v}) :
    Litex.Set.{max (u + 1) v} :=
  Set.ofType (Fn domain codomain)

/-- The exact carrier of unary functions with source-domain clauses. -/
abbrev fnSetWhere
    (domain : Litex.Set.{u})
    (codomain : Litex.Set.{v})
    (requires : {α : Litex.u.{u}} → (x : α) → In x domain → Prop) :
    Litex.Set.{max (u + 1) v} :=
  Set.ofType (FnWhere domain codomain requires)

/-- Apply a heterogeneous value known to belong to a unary function set.
Both function membership and argument membership are computational inputs to
the wrapper; Lean's ambient type alone never authorizes a Litex call. -/
noncomputable def fnApply
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    {α : Litex.u.{u}}
    {β : Litex.u.{max (u + 1) v}}
    (f : β)
    (hf : In f (fnSet domain codomain))
    (x : α)
    (hx : In x domain) :
    codomain.Carrier :=
  (In.rep f hf).call x hx

/-- Apply a function already represented by the exact `Fn` carrier. The
membership proof remains an explicit checked input, while no representative
choice is needed for the function value itself. -/
def fnApplyOwn
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    (f : Fn domain codomain)
    (_hf : In f (fnSet domain codomain))
    {α : Litex.u.{u}}
    (x : α)
    (hx : In x domain) :
    codomain.Carrier :=
  f.call x hx

/-- Apply an exact-carrier function to an exact domain-carrier value. The
function membership remains as verifier-owned evidence, while no classical
representative selection occurs for the argument. -/
def fnApplyCarrier
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    (f : Fn domain codomain)
    (_hf : In f (fnSet domain codomain))
    (x : domain.Carrier) :
    codomain.Carrier :=
  f.callOwn x

/-- Exact argument application when the function itself is selected from a
heterogeneous function-set membership certificate. -/
noncomputable def fnApplySelectedCarrier
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    {β : Litex.u.{max (u + 1) v}}
    (f : β)
    (hf : In f (fnSet domain codomain))
    (x : domain.Carrier) :
    codomain.Carrier :=
  (In.rep f hf).callOwn x

/-- Apply a heterogeneous value known to belong to a domain-constrained
function set. -/
noncomputable def fnApplyWhere
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    {requires : {α : Litex.u.{u}} → (x : α) → In x domain → Prop}
    {α : Litex.u.{u}}
    {β : Litex.u.{max (u + 1) v}}
    (f : β)
    (hf : In f (fnSetWhere domain codomain requires))
    (x : α)
    (hx : In x domain)
    (hrequires : requires x hx) :
    codomain.Carrier :=
  (In.rep f hf).call x hx hrequires

/-- Exact-carrier application for a compiler-constructed function with
source-domain clauses. -/
def fnApplyWhereOwn
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    {requires : {α : Litex.u.{u}} → (x : α) → In x domain → Prop}
    (f : FnWhere domain codomain requires)
    (_hf : In f (fnSetWhere domain codomain requires))
    {α : Litex.u.{u}}
    (x : α)
    (hx : In x domain)
    (hrequires : requires x hx) :
    codomain.Carrier :=
  f.call x hx hrequires

/-- Exact range of a total unary Litex function.  A range element retains its
native codomain value together with the heterogeneous source argument and its
checked domain membership. -/
def fnRangeOwn
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    (f : Fn domain codomain) :
    Litex.Set.{v} :=
  Set.ofType
    {value : codomain.Carrier //
      ∃ (α : Type u) (x : α) (hx : In x domain), value = f.call x hx}

/-- Exact range of a unary Litex function with a source-domain predicate. -/
def fnWhereRangeOwn
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    {requires : {α : Type u} → (x : α) → In x domain → Prop}
    (f : FnWhere domain codomain requires) :
    Litex.Set.{v} :=
  Set.ofType
    {value : codomain.Carrier //
      ∃ (α : Type u) (x : α) (hx : In x domain) (hr : requires x hx),
        value = f.call x hx hr}

/-- Every checked application of an exact total function belongs to its exact
range. -/
theorem fnApplyOwnInRange
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    (f : Fn domain codomain)
    {α : Type u}
    (x : α)
    (hx : In x domain) :
    In (f.call x hx) (fnRangeOwn f) := by
  let witness : (fnRangeOwn f).Carrier :=
    ⟨f.call x hx, ⟨α, x, hx, rfl⟩⟩
  exact ⟨witness, Same.symm (Same.subtypeNoObservation witness)⟩

/-- Inference-friendly form used when the compiler has already rendered the
exact checked application and range in the expected proposition. -/
theorem fnApplyOwnInRangeFromRenderedApplication
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    {f : Fn domain codomain}
    {hf : In f (fnSet domain codomain)}
    {alpha : Type u}
    {x : alpha}
    {hx : In x domain} :
    In (fnApplyOwn f hf x hx) (fnRangeOwn f) := by
  simpa [fnApplyOwn] using fnApplyOwnInRange f x hx

/-- Every checked application of an exact constrained function belongs to
its exact range. -/
theorem fnApplyWhereOwnInRange
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    {requires : {α : Type u} → (x : α) → In x domain → Prop}
    (f : FnWhere domain codomain requires)
    {α : Type u}
    (x : α)
    (hx : In x domain)
    (hr : requires x hx) :
    In (f.call x hx hr) (fnWhereRangeOwn f) := by
  let witness : (fnWhereRangeOwn f).Carrier :=
    ⟨f.call x hx hr, ⟨α, x, hx, hr, rfl⟩⟩
  exact ⟨witness, Same.symm (Same.subtypeNoObservation witness)⟩

/-- Inference-friendly constrained-function range introduction. -/
theorem fnApplyWhereOwnInRangeFromRenderedApplication
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    {requires : {alpha : Type u} → (x : alpha) → In x domain → Prop}
    {f : FnWhere domain codomain requires}
    {hf : In f (fnSetWhere domain codomain requires)}
    {alpha : Type u}
    {x : alpha}
    {hx : In x domain}
    {hr : requires x hx} :
    In (fnApplyWhereOwn f hf x hx hr) (fnWhereRangeOwn f) := by
  simpa [fnApplyWhereOwn] using fnApplyWhereOwnInRange f x hx hr

/-- A function range is included in its declared codomain. -/
theorem fnRangeOwnSubsetCodomain
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    (f : Fn domain codomain) :
    Subset (fnRangeOwn f) codomain := by
  intro α value membership
  rcases membership with ⟨rangeValue, sameRangeValue⟩
  exact ⟨rangeValue.val, Same.trans sameRangeValue (Same.subtypeNoObservation rangeValue)⟩

/-- A constrained function range is included in its declared codomain. -/
theorem fnWhereRangeOwnSubsetCodomain
    {domain : Litex.Set.{u}}
    {codomain : Litex.Set.{v}}
    {requires : {α : Type u} → (x : α) → In x domain → Prop}
    (f : FnWhere domain codomain requires) :
    Subset (fnWhereRangeOwn f) codomain := by
  intro α value membership
  rcases membership with ⟨rangeValue, sameRangeValue⟩
  exact ⟨rangeValue.val, Same.trans sameRangeValue (Same.subtypeNoObservation rangeValue)⟩

/-!
`FnTelescope` is the native carrier for one source application layer with any
finite number of parameters. A parameter node retains its exact Litex set and
membership proof. Later nodes may depend on the earlier value and proof, so
dependent parameter sets, domain clauses, and return sets remain explicit.
One telescope is one Litex application layer; a function-valued `done` set
starts the next source layer rather than silently currying the current one.
-/

inductive FnTelescope : Type (max 1 (v + 1)) where
  | done (codomain : Litex.Set.{v})
  | parameter
      (domain : Litex.Set)
      (next : {α : Type} → (x : α) → In x domain → FnTelescope)
  | requirement
      (condition : Prop)
      (next : condition → FnTelescope)

namespace FnTelescope

/-- Exact Lean carrier described by a source-layer telescope. -/
def Carrier : Litex.FnTelescope.{v} → Type (max 1 v)
  | .done codomain => ULift.{max 1 v, v} codomain.Carrier
  | .parameter domain next =>
      {α : Type} → (x : α) → (hx : In x domain) → Carrier (next x hx)
  | .requirement condition next =>
      (hcondition : condition) → Carrier (next hcondition)

end FnTelescope

/-- Exact Litex set of values implementing one dependent source-layer
telescope. -/
abbrev fnTelescopeSet
    (signature : Litex.FnTelescope.{v}) :
    Litex.Set.{max 1 v} :=
  Set.ofType (FnTelescope.Carrier signature)

/-- Select the exact telescope carrier from a heterogeneous membership proof.
Arguments are subsequently supplied in the source layer's retained order. -/
noncomputable def fnTelescopeApply
    {signature : Litex.FnTelescope.{v}}
    {β : Type (max 1 v)}
    (f : β)
    (hf : In f (fnTelescopeSet signature)) :
    FnTelescope.Carrier signature :=
  In.rep f hf

/-- The exact-carrier application route avoids representative choice for a
compiler-constructed telescope function while retaining the checked
membership certificate as an explicit input. -/
def fnTelescopeApplyOwn
    {signature : Litex.FnTelescope.{v}}
    (f : FnTelescope.Carrier signature)
    (_hf : In f (fnTelescopeSet signature)) :
    FnTelescope.Carrier signature :=
  f

abbrev N : Litex.Set := Set.ofType ℕ
abbrev Z : Litex.Set := Set.ofType ℤ
abbrev Q : Litex.Set := Set.ofType ℚ
abbrev R : Litex.Set := Set.ofType ℝ
abbrev C : Litex.Set := Set.ofType ℂ

/-- A real interval with independently open or closed endpoints.  Its exact
carrier is the native Mathlib real subtype satisfying the selected bounds. -/
def realInterval
    (leftClosed rightClosed : Bool)
    (start finish : ℝ) :
    Litex.Set :=
  Set.ofType
    {value : ℝ //
      (if leftClosed then start ≤ value else start < value) ∧
      (if rightClosed then value ≤ finish else value < finish)}

/-- A real ray extending rightward from one open or closed endpoint. -/
def realLeftRay
    (closed : Bool)
    (start : ℝ) :
    Litex.Set :=
  Set.ofType {value : ℝ // if closed then start ≤ value else start < value}

/-- A real ray extending leftward to one open or closed endpoint. -/
def realRightRay
    (closed : Bool)
    (finish : ℝ) :
    Litex.Set :=
  Set.ofType {value : ℝ // if closed then value ≤ finish else value < finish}

theorem realIntervalSubsetR
    (leftClosed rightClosed : Bool)
    (start finish : ℝ) :
    Subset (realInterval leftClosed rightClosed start finish) R := by
  intro α value membership
  rcases membership with ⟨intervalValue, sameIntervalValue⟩
  exact ⟨intervalValue.val,
    Same.transNoObservation sameIntervalValue
      (Same.subtypeNoObservation intervalValue)⟩

theorem realLeftRaySubsetR
    (closed : Bool)
    (start : ℝ) :
    Subset (realLeftRay closed start) R := by
  intro α value membership
  rcases membership with ⟨rayValue, sameRayValue⟩
  exact ⟨rayValue.val,
    Same.transNoObservation sameRayValue (Same.subtypeNoObservation rayValue)⟩

theorem realRightRaySubsetR
    (closed : Bool)
    (finish : ℝ) :
    Subset (realRightRay closed finish) R := by
  intro α value membership
  rcases membership with ⟨rayValue, sameRayValue⟩
  exact ⟨rayValue.val,
    Same.transNoObservation sameRayValue (Same.subtypeNoObservation rayValue)⟩

/-- Expected-type-driven finite-interval inclusion for generated proofs. -/
theorem realIntervalSubsetRFromExpectedType
    {leftClosed rightClosed : Bool}
    {start finish : ℝ} :
    Subset (realInterval leftClosed rightClosed start finish) R :=
  realIntervalSubsetR leftClosed rightClosed start finish

/-- Expected-type-driven rightward-ray inclusion for generated proofs. -/
theorem realLeftRaySubsetRFromExpectedType
    {closed : Bool}
    {start : ℝ} :
    Subset (realLeftRay closed start) R :=
  realLeftRaySubsetR closed start

/-- Expected-type-driven leftward-ray inclusion for generated proofs. -/
theorem realRightRaySubsetRFromExpectedType
    {closed : Bool}
    {finish : ℝ} :
    Subset (realRightRay closed finish) R :=
  realRightRaySubsetR closed finish

/-- A predicate-defined Litex subset. Its exact carrier is the corresponding
subtype, and the compiler-owned subtype edge relates each member to its base
value. -/
@[reducible] def setBuilder
    (base : Litex.Set.{u})
    (predicate : base.Carrier → Prop) :
    Litex.Set.{u} :=
  Set.ofType (Subtype predicate)

/-- Positive naturals use the exact subtype of native naturals carrying their
strict-positivity proof. This is not an alias of `N`: membership retains the
refining predicate in the carrier. -/
abbrev NPos : Litex.Set := setBuilder N (fun n => 0 < n)

/-- Positive rationals retain their exact native rational representative and
strict-positivity certificate. -/
abbrev QPos : Litex.Set := setBuilder Q (fun q => 0 < q)

/-- Negative integers retain their exact native integer representative and
strict-negativity certificate. -/
abbrev ZNeg : Litex.Set := setBuilder Z (fun z => z < 0)

/-- Negative rationals retain their exact native rational representative and
strict-negativity certificate. -/
abbrev QNeg : Litex.Set := setBuilder Q (fun q => q < 0)

/-- Half-open integer range with its exact Mathlib finite carrier. -/
def range (start finish : ℤ) : Litex.Set :=
  Set.ofType {z : ℤ // z ∈ Finset.Ico start finish}

/-- Closed integer range with its exact Mathlib finite carrier. -/
def closedRange (start finish : ℤ) : Litex.Set :=
  Set.ofType {z : ℤ // z ∈ Finset.Icc start finish}

theorem range_finite (start finish : ℤ) : Set.Finite (range start finish) := by
  unfold Set.Finite range
  infer_instance

theorem closedRange_finite (start finish : ℤ) :
    Set.Finite (closedRange start finish) := by
  unfold Set.Finite closedRange
  infer_instance

/-- Empty tail of a typed heterogeneous tuple/sequence spine. -/
inductive HNil : Type u where
  | nil

/-- One typed heterogeneous spine cell. The carrier type is determined by
the concrete head and tail types; no universal object is stored. -/
structure HCons (alpha : Type u) (tail : Type v) where
  head : alpha
  rest : tail

/-- Exact carrier of the empty Cartesian-product tail. Its universe is
selected by the enclosing product rather than collapsed into a universal
object carrier. -/
def cartNil : Litex.Set.{u} :=
  Set.ofType HNil.{u}

/-- Add one exact factor carrier to a Cartesian-product spine. -/
def cartCons (head tail : Litex.Set.{u}) : Litex.Set.{u} :=
  Set.ofType (HCons head.Carrier tail.Carrier)

inductive HConsDerived
    {α β tail rest : Type u} :
    HCons α tail → HCons β rest → Prop where
  | mk
      {head : α}
      {otherHead : β}
      {tailValue : tail}
      {otherTail : rest} :
      Same head otherHead →
      Same tailValue otherTail →
      HConsDerived
        (HCons.mk head tailValue)
        (HCons.mk otherHead otherTail)

instance {α β tail rest : Type u} :
    DerivedRule (HCons α tail) (HCons β rest)
      (ComplexObserver.none (HCons α tail))
      (ComplexObserver.none (HCons β rest)) where
  relation := HConsDerived
  observationEq := by intros; rfl

namespace Same

/-- Coordinatewise semantic equality for exact heterogeneous tuple spines. -/
theorem hcons
    {α β tail rest : Type u}
    {head : α}
    {otherHead : β}
    {tailValue : tail}
    {otherTail : rest}
    (headSame : Same head otherHead)
    (tailSame : Same tailValue otherTail) :
    Same
      (HCons.mk head tailValue)
      (HCons.mk otherHead otherTail) :=
  .derived (HConsDerived.mk headSame tailSame)

end Same

/-- Structural tuple evidence and its source arity. -/
class TupleShape (alpha : Type u) where
  dimension : Nat

instance : TupleShape HNil where
  dimension := 0

instance [TupleShape tail] : TupleShape (HCons alpha tail) where
  dimension := TupleShape.dimension tail + 1

def IsTuple {alpha : Type u} (_value : alpha) : Prop :=
  Nonempty (TupleShape alpha)

theorem tupleShape_isTuple [TupleShape alpha] (value : alpha) :
    IsTuple value :=
  ⟨inferInstance⟩

theorem hcons_isTuple [TupleShape tail] (head : alpha) (rest : tail) :
    IsTuple (HCons.mk head rest) :=
  ⟨inferInstance⟩

def tupleDim [TupleShape alpha] (_value : alpha) : ℂ :=
  TupleShape.dimension alpha

/-- Exact one-based index carrier for a compiler-declared indexed tuple. -/
abbrev TupleIndex (dimension : Nat) : Type :=
  {index : ℤ // index ∈ Finset.Icc 1 (dimension : ℤ)}

/-- A declared indexed tuple keeps its checked dimension at the type level and
stores one uniform exact coordinate carrier.  This is not a universal object
box: the compiler selects `alpha` from the verified coordinate expression. -/
structure IndexedTuple (dimension : Nat) (alpha : Type u) where
  coordinate : TupleIndex dimension → alpha

instance : TupleShape (IndexedTuple dimension alpha) where
  dimension := dimension

/-- Checked one-based coordinate projection. -/
def indexedTupleAt
    (tuple : IndexedTuple dimension alpha)
    (index : TupleIndex dimension) : alpha :=
  tuple.coordinate index

/-- Sequence literals use the same exact typed spine under a distinct wrapper
so tuple-only facts cannot be inferred from a sequence by Lean typing. -/
structure SequenceLiteral (payload : Type u) where
  value : payload

def sequenceSet (values : Litex.Set.{u}) :=
  fnSet NPos values

/-- The archived compiler only exposed the following higher constructors as
proof-free object terms plus reflexive equality. Their native ABI therefore
uses operator-specific typed syntax values until a verifier-owned semantic
membership adapter is selected; this is deliberately not a universal object
box. -/
structure BigUnionExpr (family : Type u) where
  source : family

structure BigIntersectExpr (family : Type u) where
  source : family

def bigUnion (family : alpha) : BigUnionExpr alpha := ⟨family⟩
def bigIntersect (family : alpha) : BigIntersectExpr alpha := ⟨family⟩

structure GeneralCartExpr (index : Type u) (family : Type v) (selector : Type w) where
  indexSet : index
  familySet : family
  familyFunction : selector

def generalCart (index : alpha) (family : beta) (selector : gamma) :
    GeneralCartExpr alpha beta gamma :=
  ⟨index, family, selector⟩

/-- The mathematical value of a Litex sum over the inclusive integer interval.
The summand consumes its exact `Z` membership proof and returns the exact
codomain carrier. -/
noncomputable def integerRangeSum
    {codomain : Litex.Set}
    [AddCommMonoid codomain.Carrier]
    (start finish : ℤ)
    (function : Litex.Fn Litex.Z codomain) :
    codomain.Carrier :=
  ∑ k ∈ Finset.Icc start finish, function.callOwn k

/-- Source `sum` has one semantic meaning: inclusive integer-range summation. -/
noncomputable def sum
    {codomain : Litex.Set}
    [AddCommMonoid codomain.Carrier]
    (start finish : ℤ)
    (function : Litex.Fn Litex.Z codomain) :
    codomain.Carrier :=
  integerRangeSum start finish function

structure ProductExpr (start : Type u) (finish : Type v) (function : Type w) where
  lower : start
  upper : finish
  body : function

def product (start : alpha) (finish : beta) (function : gamma) :
    ProductExpr alpha beta gamma :=
  ⟨start, finish, function⟩

structure ReduceExpr
    (start : Type u) (finish : Type v) (function : Type w)
    (operation : Type x) (seed : Type y) where
  lower : start
  upper : finish
  body : function
  reducer : operation
  initial : seed

def reduce (start : alpha) (finish : beta) (function : gamma)
    (operation : delta) (seed : epsilon) :
    ReduceExpr alpha beta gamma delta epsilon :=
  ⟨start, finish, function, operation, seed⟩

structure FiniteSumExpr (set : Type u) (function : Type v) where
  sourceSet : set
  body : function

def finiteSetSum (set : alpha) (function : beta) : FiniteSumExpr alpha beta :=
  ⟨set, function⟩

structure FiniteProductExpr (set : Type u) (function : Type v) where
  sourceSet : set
  body : function

def finiteSetProduct (set : alpha) (function : beta) : FiniteProductExpr alpha beta :=
  ⟨set, function⟩

structure FiniteReduceExpr
    (set : Type u) (function : Type v) (operation : Type w) (seed : Type x) where
  sourceSet : set
  body : function
  reducer : operation
  initial : seed

def finiteSetReduce (set : alpha) (function : beta) (operation : gamma) (seed : delta) :
    FiniteReduceExpr alpha beta gamma delta :=
  ⟨set, function, operation, seed⟩

/-- Positive reals use the exact subtype of native reals carrying their
strict-positivity proof. -/
abbrev RPos : Litex.Set := setBuilder R (fun r => 0 < r)

/-- Negative reals retain their exact native real representative and
strict-negativity certificate. -/
abbrev RNeg : Litex.Set := setBuilder R (fun r => r < 0)

/-- Nonzero integers retain a complex source representative together with the
exact integer-membership and semantic-nonzero certificates used by Litex. -/
abbrev ZStar : Litex.Set :=
  setBuilder C (fun z => In z Z ∧
    ¬ @Same ℂ ℂ
      (ComplexObserver.none ℂ) (ComplexObserver.none ℂ) z (0 : ℂ))

/-- Nonzero rationals retain a complex source representative together with the
exact rational-membership and semantic-nonzero certificates used by Litex. -/
abbrev QStar : Litex.Set :=
  setBuilder C (fun z => In z Q ∧
    ¬ @Same ℂ ℂ
      (ComplexObserver.none ℂ) (ComplexObserver.none ℂ) z (0 : ℂ))

/-- Nonzero reals retain a complex source representative together with the
exact real-membership and semantic-nonzero certificates used by Litex. -/
abbrev RStar : Litex.Set :=
  setBuilder C (fun z => In z R ∧
    ¬ @Same ℂ ℂ
      (ComplexObserver.none ℂ) (ComplexObserver.none ℂ) z (0 : ℂ))

/-- Nonzero complexes retain a complex source representative together with the
exact complex-membership and semantic-nonzero certificates used by Litex. -/
abbrev CStar : Litex.Set :=
  setBuilder C (fun z => In z C ∧
    ¬ @Same ℂ ℂ
      (ComplexObserver.none ℂ) (ComplexObserver.none ℂ) z (0 : ℂ))

/-!
The ordered-numeric layer deliberately lives at Lean universe `0`: Mathlib's
native `ℕ`, `ℤ`, `ℚ`, `ℝ`, and `ℂ` all live there. This does not restrict the
universe-polymorphic `Litex.Set`, `Litex.In`, or `Litex.Same` interfaces.

The built-in primitive and native-operation representation edges are declared
in this public header. Facts which only transport a chosen real representative need no global
assumption. General order does not compare independently selected
representatives: it uses the one canonical real observation of the compiler's
current numeric carrier, `Complex.re`, and therefore reduces directly to
Mathlib order.
-/

/-- `x` has the real representative `r` when Litex semantic equality relates
the (possibly differently typed) value `x` to the native Mathlib real `r`. -/
def AsReal {α : Type} (x : α) (r : ℝ) : Prop :=
  @Same α ℝ
    (ComplexObserver.none α)
    (ComplexObserver.none ℝ)
    x r

namespace AsReal

theorem real (r : ℝ) : AsReal r r :=
  Same.reflNoObservation r

theorem complex (r : ℝ) : AsReal (r : ℂ) r :=
  Same.complexRealNoObservation r

theorem nat (n : ℕ) : AsReal n (n : ℝ) :=
  Same.transNoObservation
    (Same.natComplexNoObservation n)
    (Same.complexRealNoObservation (n : ℝ))

theorem int (z : ℤ) : AsReal z (z : ℝ) :=
  Same.transNoObservation
    (Same.intComplexNoObservation z)
    (Same.complexRealNoObservation (z : ℝ))

theorem rat (q : ℚ) : AsReal q (q : ℝ) :=
  Same.transNoObservation
    (Same.ratComplexNoObservation q)
    (Same.complexRealNoObservation (q : ℝ))

/-- Semantic equality transports a chosen real representative. -/
theorem congr
    {α β : Type}
    {x : α}
    {y : β}
    {r : ℝ}
    (hxy : @Same α β
      (ComplexObserver.none α)
      (ComplexObserver.none β)
      x y) :
    AsReal x r ↔ AsReal y r := by
  constructor
  · intro hxr
    exact Same.transNoObservation (Same.symmNoObservation hxy) hxr
  · intro hyr
    exact Same.transNoObservation hxy hyr

/-- Values with the same real representative are semantically equal. -/
theorem same
    {α β : Type}
    {x : α}
    {y : β}
    {r : ℝ}
    (hxr : AsReal x r)
    (hyr : AsReal y r) :
    @Same α β
      (ComplexObserver.none α)
      (ComplexObserver.none β)
      x y :=
  Same.transNoObservation hxr (Same.symmNoObservation hyr)

end AsReal

/-- Membership in `R` is exactly existence of a real representative. -/
theorem inR_iff_asReal
    {α : Type}
    {x : α} :
    In x R ↔ ∃ r : ℝ, AsReal x r :=
  Iff.rfl

/-!
Zero-ended source comparisons use a canonical Mathlib zero instead of
selecting a second real representative for the Litex numeral `0`. This is the
constructive order bridge used by sign rules: a proof of `0 < x` or `0 ≤ x`
contains exactly one representative of `x`, and its order certificate is an
ordinary Mathlib real inequality.
-/

/-- Canonical lowering of a source comparison `0 < x`. -/
def Positive
    {α : Type}
    (x : α) : Prop :=
  ∃ r : ℝ, AsReal x r ∧ 0 < r

/-- Canonical lowering of a source comparison `0 ≤ x`. -/
def Nonnegative
    {α : Type}
    (x : α) : Prop :=
  ∃ r : ℝ, AsReal x r ∧ 0 ≤ r

/-- Canonical lowering of a source comparison `x ≤ 0`. Like
`Nonnegative`, this owns the one real representative selected for `x`; it is
not reconstructed from an unrelated `Complex.re` observation. -/
def Nonpositive
    {α : Type}
    (x : α) : Prop :=
  ∃ r : ℝ, AsReal x r ∧ r ≤ 0

/-- Canonical lowering of a source comparison `x < 0`. Like `Positive`, this
owns one selected real representative and therefore transports soundly across
Litex semantic equality. -/
def Negative
    {α : Type}
    (x : α) : Prop :=
  ∃ r : ℝ, AsReal x r ∧ r < 0

namespace Positive

theorem intro
    {α : Type}
    {x : α}
    {r : ℝ}
    (hxr : AsReal x r)
    (hr : 0 < r) :
    Positive x :=
  ⟨r, hxr, hr⟩

theorem toNonnegative
    {α : Type}
    {x : α}
    (hx : Positive x) :
    Nonnegative x := by
  rcases hx with ⟨r, hxr, hr⟩
  exact ⟨r, hxr, le_of_lt hr⟩

theorem congr
    {α β : Type}
    {x : α}
    {y : β}
    (hxy : Same x y) :
    Positive x ↔ Positive y := by
  constructor
  · rintro ⟨r, hxr, hr⟩
    exact ⟨r, (AsReal.congr hxy).mp hxr, hr⟩
  · rintro ⟨r, hyr, hr⟩
    exact ⟨r, (AsReal.congr hxy).mpr hyr, hr⟩

end Positive

namespace Nonnegative

theorem intro
    {α : Type}
    {x : α}
    {r : ℝ}
    (hxr : AsReal x r)
    (hr : 0 ≤ r) :
    Nonnegative x :=
  ⟨r, hxr, hr⟩

theorem congr
    {α β : Type}
    {x : α}
    {y : β}
    (hxy : Same x y) :
    Nonnegative x ↔ Nonnegative y := by
  constructor
  · rintro ⟨r, hxr, hr⟩
    exact ⟨r, (AsReal.congr hxy).mp hxr, hr⟩
  · rintro ⟨r, hyr, hr⟩
    exact ⟨r, (AsReal.congr hxy).mpr hyr, hr⟩

end Nonnegative

namespace Nonpositive

theorem intro
    {α : Type}
    {x : α}
    {r : ℝ}
    (hxr : AsReal x r)
    (hr : r ≤ 0) :
    Nonpositive x :=
  ⟨r, hxr, hr⟩

theorem congr
    {α β : Type}
    {x : α}
    {y : β}
    (hxy : Same x y) :
    Nonpositive x ↔ Nonpositive y := by
  constructor
  · rintro ⟨r, hxr, hr⟩
    exact ⟨r, (AsReal.congr hxy).mp hxr, hr⟩
  · rintro ⟨r, hyr, hr⟩
    exact ⟨r, (AsReal.congr hxy).mpr hyr, hr⟩

end Nonpositive

namespace Negative

theorem intro
    {α : Type}
    {x : α}
    {r : ℝ}
    (hxr : AsReal x r)
    (hr : r < 0) :
  Negative x :=
  ⟨r, hxr, hr⟩

theorem toNonpositive
    {α : Type}
    {x : α}
    (hx : Negative x) :
    Nonpositive x := by
  rcases hx with ⟨r, hxr, hr⟩
  exact ⟨r, hxr, le_of_lt hr⟩

theorem congr
    {α β : Type}
    {x : α}
    {y : β}
    (hxy : Same x y) :
    Negative x ↔ Negative y := by
  constructor
  · rintro ⟨r, hxr, hr⟩
    exact ⟨r, (AsReal.congr hxy).mp hxr, hr⟩
  · rintro ⟨r, hyr, hr⟩
    exact ⟨r, (AsReal.congr hxy).mpr hyr, hr⟩

end Negative

/-- The canonical Mathlib-ordered observation of a compiled Litex numeric
object. Source admission into the ordered-real fragment is verifier-owned;
once admitted, every occurrence of the same `ℕ`/`ℤ`/`ℚ`/`ℝ`-lowered complex
term has exactly this one observation. -/
def OrderValue (z : ℂ) : ℝ :=
  z.re

/-- The reviewed target representation of source `abs`. Litex admits this
operator only after checking that its argument is real; keeping the target
operation total on `ℂ` lets object rendering remain proof-independent while
agreeing definitionally with Mathlib absolute value on every admitted real
argument. -/
noncomputable def abs (z : ℂ) : ℂ :=
  ((‖z‖ : ℝ) : ℂ)

/-- The reviewed target representation of source binary `min`. Source
well-definedness owns realness; the target operation uses the canonical real
observation already used by `Litex.Le`. -/
def min (x y : ℂ) : ℂ :=
  ((Min.min (OrderValue x) (OrderValue y) : ℝ) : ℂ)

/-- The reviewed target representation of source binary `max`. -/
def max (x y : ℂ) : ℂ :=
  ((Max.max (OrderValue x) (OrderValue y) : ℝ) : ℂ)

/-- Litex strict order on its current numeric carrier. This is a custom Litex
relation with a definitional route to Mathlib's native real order. -/
def Lt (x y : ℂ) : Prop :=
  OrderValue x < OrderValue y

/-- Litex non-strict order on its current numeric carrier. -/
def Le (x y : ℂ) : Prop :=
  OrderValue x ≤ OrderValue y

/-- Native real values which are heterogeneous members of a Litex set.  This
is the representation-independent set used by completeness: it does not
trust a target-rendering observer to prove source membership. -/
def realMemberValues (set : Litex.Set) : _root_.Set ℝ :=
  {value | Litex.In value set}

/-- The real-member set paired with the checked subset certificate.  The
certificate is retained in the LUB/GLB proposition, while the extension is
defined solely by `In`, so all producers and consumers use the same values. -/
def realSubsetMemberValues
    (set : Litex.Set)
    (_setSubsetReal : Litex.Subset set Litex.R) : _root_.Set ℝ :=
  realMemberValues set

/-- A verifier-owned least-upper-bound certificate over the native real values
which actually belong to the Litex set. -/
def RealLeastUpperBound (set : Litex.Set) (candidate : ℂ) : Prop :=
  ∃ setSubsetReal : Litex.Subset set Litex.R,
    IsLUB (realSubsetMemberValues set setSubsetReal) (OrderValue candidate)

/-- Greatest-lower-bound certificate dual to `RealLeastUpperBound`. -/
def RealGreatestLowerBound (set : Litex.Set) (candidate : ℂ) : Prop :=
  ∃ setSubsetReal : Litex.Subset set Litex.R,
    IsGLB (realSubsetMemberValues set setSubsetReal) (OrderValue candidate)

/-- A bounded positive-natural function parameter is compared through one
source complex observation. This keeps the telescope requirement usable for a
heterogeneous argument while retaining the exact Litex `index <= length`
premise supplied by statement verification. -/
def positiveNaturalParameterLessEqualNaturalBound
    {α : Type}
    (index : α)
    (length : Nat) :
    Prop :=
  ∃ complexIndex : Complex,
    @Litex.Same α Complex
      (ComplexObserver.none α)
      (ComplexObserver.none Complex)
      index complexIndex ∧
      Litex.Le complexIndex (length : Complex)

theorem positiveNaturalParameterLessEqualNaturalBoundOfComplex
    {index : Complex}
    {length : Nat}
    (indexLessEqualLength : Litex.Le index (length : Complex)) :
    positiveNaturalParameterLessEqualNaturalBound index length :=
  ⟨index, Litex.Same.reflNoObservation index, indexLessEqualLength⟩

/-- One finite sequence is exactly the positive-natural function telescope
whose retained source-domain clause bounds the index by `length`. The
membership proof for the `N+` parameter selects the native natural used by
that clause; no zero-based `Fin` carrier silently changes source indexing. -/
def finiteSequenceSignature
    (values : Litex.Set.{u})
    (length : Nat) :
  Litex.FnTelescope.{u} :=
  .parameter Litex.NPos (fun {_alpha : Type} index _indexMembership =>
    .requirement
      (positiveNaturalParameterLessEqualNaturalBound index length)
      (fun _ => .done values))

def finiteSequenceSet (values : Litex.Set.{u}) (length : Nat) :=
  Litex.fnTelescopeSet (finiteSequenceSignature values length)

/-- A matrix is one source application layer with two positive-natural
parameters and the two retained one-based bounds. -/
def matrixSignature
    (values : Litex.Set.{u})
    (rowCount columnCount : Nat) :
    Litex.FnTelescope.{u} :=
  .parameter Litex.NPos (fun {_rowAlpha : Type} row _rowMembership =>
    .parameter Litex.NPos (fun {_columnAlpha : Type} column _columnMembership =>
      .requirement
        (positiveNaturalParameterLessEqualNaturalBound row rowCount ∧
          positiveNaturalParameterLessEqualNaturalBound column columnCount)
        (fun _ => .done values)))

def matrixSet
    (values : Litex.Set.{u})
    (rowCount columnCount : Nat) :=
  Litex.fnTelescopeSet (matrixSignature values rowCount columnCount)

namespace Lt

theorem intro
    {x y : ℂ}
    (hxy : OrderValue x < OrderValue y) :
    Lt x y :=
  hxy

theorem toLe
    {x y : ℂ}
    (h : Lt x y) :
    Le x y :=
  le_of_lt h

theorem irrefl
    (x : ℂ) :
    ¬ Lt x x :=
  lt_irrefl (OrderValue x)

theorem trans
    {x y z : ℂ}
    (hxy : Lt x y)
    (hyz : Lt y z) :
    Lt x z :=
  lt_trans hxy hyz

theorem transLe
    {x y z : ℂ}
    (hxy : Lt x y)
    (hyz : Le y z) :
    Lt x z :=
  lt_of_lt_of_le hxy hyz

end Lt

namespace Le

theorem intro
    {x y : ℂ}
    (hxy : OrderValue x ≤ OrderValue y) :
    Le x y :=
  hxy

theorem refl (x : ℂ) : Le x x :=
  le_refl (OrderValue x)

theorem reflOfAsReal
    {x : ℂ}
    {r : ℝ}
    (_hxr : AsReal x r) :
    Le x x :=
  refl x

theorem reflOfInR
    {x : ℂ}
    (_hx : In x R) :
    Le x x :=
  refl x

theorem trans
    {x y z : ℂ}
    (hxy : Le x y)
    (hyz : Le y z) :
    Le x z :=
  le_trans hxy hyz

theorem transLt
    {x y z : ℂ}
    (hxy : Le x y)
    (hyz : Lt y z) :
    Lt x z :=
  lt_of_le_of_lt hxy hyz

end Le

namespace OrderBridge

/-- A native Mathlib real inequality introduces a Litex inequality without
any global coherence assumption. -/
theorem ltOfReal
    {r s : ℝ}
    (h : r < s) :
    Lt (r : ℂ) (s : ℂ) := by
  simpa [Lt, OrderValue] using h

theorem leOfReal
    {r s : ℝ}
    (h : r ≤ s) :
    Le (r : ℂ) (s : ℂ) := by
  simpa [Le, OrderValue] using h

theorem ltOfComplexReals
    {r s : ℝ}
    (h : r < s) :
    Lt (r : ℂ) (s : ℂ) :=
  ltOfReal h

theorem leOfComplexReals
    {r s : ℝ}
    (h : r ≤ s) :
    Le (r : ℂ) (s : ℂ) :=
  leOfReal h

theorem positiveOfComplexReal
    {r : ℝ}
    (h : 0 < r) :
    Positive (r : ℂ) :=
  Positive.intro (AsReal.complex r) h

theorem nonnegativeOfComplexReal
    {r : ℝ}
    (h : 0 ≤ r) :
    Nonnegative (r : ℂ) :=
  Nonnegative.intro (AsReal.complex r) h

theorem real_lt_iff
    {r s : ℝ} :
    Lt (r : ℂ) (s : ℂ) ↔ r < s := by
  simp [Lt, OrderValue]

theorem real_le_iff
    {r s : ℝ} :
    Le (r : ℂ) (s : ℂ) ↔ r ≤ s := by
  simp [Le, OrderValue]

end OrderBridge

/-- The current compiler numeric carrier's exact natural-primality wrapper.
The equality conjunct prevents a non-natural complex value from being
classified through truncation or a host-language coercion. -/
def Prime (value : ℂ) : Prop :=
  ∃ natural : ℕ, value = (natural : ℂ) ∧ Nat.Prime natural

/-- Exact natural coprimality on the current complex-valued compiler carrier. -/
def Coprime (left right : ℂ) : Prop :=
  ∃ leftNatural rightNatural : ℕ,
    left = (leftNatural : ℂ) ∧
      right = (rightNatural : ℂ) ∧
        Nat.Coprime leftNatural rightNatural

theorem primeOfNat (natural : ℕ) (prime : Nat.Prime natural) :
    Prime (natural : ℂ) :=
  ⟨natural, rfl, prime⟩

theorem notPrimeOfNat (natural : ℕ) (notPrime : ¬ Nat.Prime natural) :
    ¬ Prime (natural : ℂ) := by
  rintro ⟨other, equalCast, otherPrime⟩
  have equalNatural : natural = other := by
    exact_mod_cast equalCast
  exact notPrime (equalNatural ▸ otherPrime)

theorem coprimeOfNat
    (left right : ℕ)
    (coprime : Nat.Coprime left right) :
    Coprime (left : ℂ) (right : ℂ) :=
  ⟨left, right, rfl, rfl, coprime⟩

theorem notCoprimeOfNat
    (left right : ℕ)
    (notCoprime : ¬ Nat.Coprime left right) :
    ¬ Coprime (left : ℂ) (right : ℂ) := by
  rintro ⟨otherLeft, otherRight, equalLeftCast, equalRightCast, otherCoprime⟩
  have equalLeft : left = otherLeft := by
    exact_mod_cast equalLeftCast
  have equalRight : right = otherRight := by
    exact_mod_cast equalRightCast
  exact notCoprime (equalLeft ▸ equalRight ▸ otherCoprime)

end Litex
