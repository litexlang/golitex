/-
The same mathematics as `main.lit`, expressed in pure Lean 4.

Lean's Prelude has products but no vector-space hierarchy, so the scalar
operations used by this R²-style model are explicit setting fields. This is
handwritten comparison code, not compiler output.
-/

universe u

namespace LinearAlgebraSameMathInLean

structure ScalarSetting (R : Type u) where
  zero : R
  add : R → R → R
  mul : R → R → R
  sub : R → R → R
  zero_add : add zero zero = zero
  mul_zero : ∀ a, mul a zero = zero
  sub_self : ∀ a, sub a a = zero
  sub_eq_zero : ∀ {a b}, sub a b = zero → a = b

theorem congrArg2 {X Y : Type} {Z : Sort _} (f : X → Y → Z)
    {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    f x₁ y₁ = f x₂ y₂ := by
  cases hx
  cases hy
  rfl

abbrev Vec2 (R : Type u) := R × R

def vectorAdd (S : ScalarSetting R) (u v : Vec2 R) : Vec2 R :=
  (S.add u.1 v.1, S.add u.2 v.2)

def scalarMul (S : ScalarSetting R) (a : R) (v : Vec2 R) : Vec2 R :=
  (S.mul a v.1, S.mul a v.2)

def zeroVector (S : ScalarSetting R) : Vec2 R := (S.zero, S.zero)

def vectorSub (S : ScalarSetting R) (u v : Vec2 R) : Vec2 R :=
  (S.sub u.1 v.1, S.sub u.2 v.2)

structure LinearMap (S : ScalarSetting R) where
  toFun : Vec2 R → R
  map_add : ∀ u v, toFun (vectorAdd S u v) = S.add (toFun u) (toFun v)
  map_smul : ∀ a v, toFun (scalarMul S a v) = S.mul a (toFun v)
  map_sub : ∀ u v, toFun (vectorSub S u v) = S.sub (toFun u) (toFun v)
  map_zero : toFun (zeroVector S) = S.zero

def projectionX (S : ScalarSetting R) : LinearMap S where
  toFun v := v.1
  map_add := by intro u v; rfl
  map_smul := by intro a v; rfl
  map_sub := by intro u v; rfl
  map_zero := rfl

def Kernel (S : ScalarSetting R) (T : LinearMap S) : Vec2 R → Prop :=
  fun v => T.toFun v = S.zero

structure Subspace (S : ScalarSetting R) where
  carrier : Vec2 R → Prop
  zero_mem : carrier (zeroVector S)
  add_mem : ∀ {u v}, carrier u → carrier v → carrier (vectorAdd S u v)
  smul_mem : ∀ a {v}, carrier v → carrier (scalarMul S a v)

def kernelSubspace (S : ScalarSetting R) (T : LinearMap S) : Subspace S where
  carrier := Kernel S T
  zero_mem := T.map_zero
  add_mem := by
    intro u v hu hv
    calc
      T.toFun (vectorAdd S u v) = S.add (T.toFun u) (T.toFun v) := T.map_add u v
      _ = S.add S.zero S.zero := congrArg2 S.add hu hv
      _ = S.zero := S.zero_add
  smul_mem := by
    intro a v hv
    calc
      T.toFun (scalarMul S a v) = S.mul a (T.toFun v) := T.map_smul a v
      _ = S.mul a S.zero := congrArg (S.mul a) hv
      _ = S.zero := S.mul_zero a

def IsInjective (T : LinearMap S) : Prop :=
  ∀ u v, T.toFun u = T.toFun v → u = v

def ZeroSubspace (S : ScalarSetting R) : Vec2 R → Prop :=
  fun v => v = zeroVector S

theorem injective_linear_map_has_trivial_kernel
    (S : ScalarSetting R) (T : LinearMap S) (hinjective : IsInjective T) :
    ∀ v, Kernel S T v ↔ ZeroSubspace S v := by
  intro v
  constructor
  · intro hv
    apply hinjective v (zeroVector S)
    exact hv.trans T.map_zero.symm
  · intro hv
    change v = zeroVector S at hv
    exact hv ▸ T.map_zero

theorem trivial_kernel_implies_injective
    (S : ScalarSetting R) (T : LinearMap S)
    (trivialKernel : ∀ v, Kernel S T v ↔ ZeroSubspace S v) :
    IsInjective T := by
  intro u v huv
  have difference_in_kernel : Kernel S T (vectorSub S u v) := by
    calc
      T.toFun (vectorSub S u v) = S.sub (T.toFun u) (T.toFun v) := T.map_sub u v
      _ = S.sub (T.toFun u) (T.toFun u) :=
        congrArg (S.sub (T.toFun u)) huv.symm
      _ = S.zero := S.sub_self (T.toFun u)
  have difference_is_zero : vectorSub S u v = zeroVector S :=
    (trivialKernel (vectorSub S u v)).mp difference_in_kernel
  apply Prod.ext
  · apply S.sub_eq_zero
    exact congrArg Prod.fst difference_is_zero
  · apply S.sub_eq_zero
    exact congrArg Prod.snd difference_is_zero

theorem projection_x_is_not_injective
    (S : ScalarSetting R) {nonzero : R} (hne : nonzero ≠ S.zero) :
    ¬ IsInjective (projectionX S) := by
  intro hinjective
  have pair_equality : (S.zero, nonzero) = (S.zero, S.zero) :=
    hinjective (S.zero, nonzero) (S.zero, S.zero) rfl
  have second_coordinate_equality : nonzero = S.zero :=
    congrArg Prod.snd pair_equality
  exact hne second_coordinate_equality

end LinearAlgebraSameMathInLean
