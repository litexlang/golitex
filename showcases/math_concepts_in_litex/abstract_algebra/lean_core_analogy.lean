/-
Pure Lean 4 analogy for `main.lit`.

This file deliberately has no imports: it uses only Lean's automatically
loaded Prelude. It is a handwritten comparison, not compiler-generated output
and not a statement about the current Litex-to-Lean compiler's supported ABI.

The `Group` structure is the Lean counterpart of the Litex `GroupSetting`: it
packages the operations and laws that remain implicit inside each named Litex
setting.
-/

universe u v

structure Group (A : Type u) where
  mul : A → A → A
  one : A
  inv : A → A
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  inv_mul : ∀ a, mul (inv a) a = one
  mul_inv : ∀ a, mul a (inv a) = one

namespace Group

theorem congrArg2 {X : Type u} {Y : Type v} {Z : Sort _}
    (f : X → Y → Z) {x₁ x₂ : X} {y₁ y₂ : Y}
    (hx : x₁ = x₂) (hy : y₁ = y₂) : f x₁ y₁ = f x₂ y₂ := by
  cases hx
  cases hy
  rfl

theorem left_cancel {A : Type u} (G : Group A) {a b c : A}
    (h : G.mul a b = G.mul a c) : b = c := by
  calc
    b = G.mul G.one b := (G.one_mul b).symm
    _ = G.mul (G.mul (G.inv a) a) b :=
      congrArg (fun x => G.mul x b) (G.inv_mul a).symm
    _ = G.mul (G.inv a) (G.mul a b) := G.mul_assoc (G.inv a) a b
    _ = G.mul (G.inv a) (G.mul a c) :=
      congrArg (fun x => G.mul (G.inv a) x) h
    _ = G.mul (G.mul (G.inv a) a) c := (G.mul_assoc (G.inv a) a c).symm
    _ = G.mul G.one c := congrArg (fun x => G.mul x c) (G.inv_mul a)
    _ = c := G.one_mul c

theorem identity_unique {A : Type u} (G : Group A) (identity : A)
    (_left_identity : ∀ a, G.mul identity a = a)
    (right_identity : ∀ a, G.mul a identity = a) : identity = G.one := by
  calc
    identity = G.mul G.one identity := (G.one_mul identity).symm
    _ = G.one := right_identity G.one

theorem inverse_unique {A : Type u} (G : Group A) {a b : A}
    (h : G.mul b a = G.one) : b = G.inv a := by
  calc
    b = G.mul b G.one := (G.mul_one b).symm
    _ = G.mul b (G.mul a (G.inv a)) :=
      congrArg (fun x => G.mul b x) (G.mul_inv a).symm
    _ = G.mul (G.mul b a) (G.inv a) := (G.mul_assoc b a (G.inv a)).symm
    _ = G.mul G.one (G.inv a) := congrArg (fun x => G.mul x (G.inv a)) h
    _ = G.inv a := G.one_mul (G.inv a)

structure Hom {A : Type u} {B : Type v} (G : Group A) (H : Group B) where
  toFun : A → B
  map_mul : ∀ x y, toFun (G.mul x y) = H.mul (toFun x) (toFun y)

theorem Hom.map_one {A : Type u} {B : Type v}
    {G : Group A} {H : Group B} (f : Hom G H) :
    f.toFun G.one = H.one := by
  have image_is_idempotent :
      H.mul (f.toFun G.one) (f.toFun G.one) = f.toFun G.one := by
    calc
      H.mul (f.toFun G.one) (f.toFun G.one) =
          f.toFun (G.mul G.one G.one) := (f.map_mul G.one G.one).symm
      _ = f.toFun G.one := congrArg f.toFun (G.one_mul G.one)

  have cancellable_equality :
      H.mul (f.toFun G.one) (f.toFun G.one) =
        H.mul (f.toFun G.one) H.one :=
    image_is_idempotent.trans (H.mul_one (f.toFun G.one)).symm

  exact left_cancel H cancellable_equality

theorem Hom.map_inv {A : Type u} {B : Type v}
    {G : Group A} {H : Group B} (f : Hom G H) (a : A) :
    f.toFun (G.inv a) = H.inv (f.toFun a) := by
  have image_is_left_inverse :
      H.mul (f.toFun (G.inv a)) (f.toFun a) = H.one := by
    calc
      H.mul (f.toFun (G.inv a)) (f.toFun a) =
          f.toFun (G.mul (G.inv a) a) := (f.map_mul (G.inv a) a).symm
      _ = f.toFun G.one := congrArg f.toFun (G.inv_mul a)
      _ = H.one := f.map_one

  exact inverse_unique H image_is_left_inverse

/- A pure Lean set can be represented directly by its predicate `A → Prop`. -/
structure Subgroup {A : Type u} (G : Group A) where
  carrier : A → Prop
  one_mem : carrier G.one
  mul_mem : ∀ {x y}, carrier x → carrier y → carrier (G.mul x y)
  inv_mem : ∀ {x}, carrier x → carrier (G.inv x)

def IsNormal {A : Type u} (G : Group A) (K : Subgroup G) : Prop :=
  ∀ a h, K.carrier h → K.carrier (G.mul (G.mul a h) (G.inv a))

def Hom.kernel {A : Type u} {B : Type v}
    {G : Group A} {H : Group B} (f : Hom G H) : Subgroup G where
  carrier x := f.toFun x = H.one
  one_mem := f.map_one
  mul_mem := by
    intro x y hx hy
    calc
      f.toFun (G.mul x y) = H.mul (f.toFun x) (f.toFun y) := f.map_mul x y
      _ = H.mul H.one H.one := congrArg2 H.mul hx hy
      _ = H.one := H.one_mul H.one
  inv_mem := by
    intro x hx
    calc
      f.toFun (G.inv x) = H.inv (f.toFun x) := f.map_inv x
      _ = H.inv H.one := congrArg H.inv hx
      _ = H.one := (inverse_unique H (H.one_mul H.one)).symm

theorem Hom.kernel_is_normal {A : Type u} {B : Type v}
    {G : Group A} {H : Group B} (f : Hom G H) :
    IsNormal G f.kernel := by
  intro conjugator kernelElement kernelElement_mem
  change f.toFun kernelElement = H.one at kernelElement_mem
  change f.toFun (G.mul (G.mul conjugator kernelElement) (G.inv conjugator)) = H.one

  have maps_conjugator_inverse :
      f.toFun (G.inv conjugator) = H.inv (f.toFun conjugator) :=
    f.map_inv conjugator

  calc
    f.toFun (G.mul (G.mul conjugator kernelElement) (G.inv conjugator)) =
        H.mul (f.toFun (G.mul conjugator kernelElement))
          (f.toFun (G.inv conjugator)) :=
      f.map_mul (G.mul conjugator kernelElement) (G.inv conjugator)
    _ = H.mul (H.mul (f.toFun conjugator) (f.toFun kernelElement))
          (H.inv (f.toFun conjugator)) :=
      congrArg2 H.mul (f.map_mul conjugator kernelElement) maps_conjugator_inverse
    _ = H.mul (H.mul (f.toFun conjugator) H.one)
          (H.inv (f.toFun conjugator)) :=
      congrArg
        (fun x => H.mul (H.mul (f.toFun conjugator) x)
          (H.inv (f.toFun conjugator)))
        kernelElement_mem
    _ = H.mul (f.toFun conjugator) (H.inv (f.toFun conjugator)) :=
      congrArg (fun x => H.mul x (H.inv (f.toFun conjugator)))
        (H.mul_one (f.toFun conjugator))
    _ = H.one := H.mul_inv (f.toFun conjugator)

end Group
