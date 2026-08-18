/-
The same mathematics as `main.lit`, expressed with only Lean 4's Prelude.
This is handwritten comparison code, not compiler output.
-/

universe u v w

namespace LinearAlgebraSameMathInLean

theorem congrArg2 {X : Sort u} {Y : Sort v} {Z : Sort w} (f : X → Y → Z)
    {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    f x₁ y₁ = f x₂ y₂ := by
  cases hx
  cases hy
  rfl

structure Field (K : Type u) where
  zero : K
  one : K
  add : K → K → K
  neg : K → K
  mul : K → K → K
  inv : K → K
  zero_ne_one : zero ≠ one
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_add : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  add_comm : ∀ x y, add x y = add y x
  mul_comm : ∀ x y, mul x y = mul y x
  zero_add : ∀ x, add zero x = x
  add_neg : ∀ x, add x (neg x) = zero
  one_mul : ∀ x, mul one x = x
  mul_inv : ∀ x, x ≠ zero → mul x (inv x) = one

structure VectorSpace (K : Type u) (V : Type v) where
  field : Field K
  zero : V
  add : V → V → V
  smul : K → V → V
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  add_comm : ∀ x y, add x y = add y x
  zero_add : ∀ x, add zero x = x
  neg_exists : ∀ x, ∃ y, add x y = zero
  smul_mul : ∀ a b x, smul (field.mul a b) x = smul a (smul b x)
  add_smul : ∀ a b x, smul (field.add a b) x = add (smul a x) (smul b x)
  smul_add : ∀ a x y, smul a (add x y) = add (smul a x) (smul a y)
  one_smul : ∀ x, smul field.one x = x

noncomputable def vectorNeg (space : VectorSpace K V) (x : V) : V :=
  Classical.choose (space.neg_exists x)

theorem vectorNeg_spec (space : VectorSpace K V) (x : V) :
    space.add x (vectorNeg space x) = space.zero :=
  Classical.choose_spec (space.neg_exists x)

noncomputable def vectorSub (space : VectorSpace K V) (x y : V) : V :=
  space.add x (vectorNeg space y)

theorem add_left_cancel (space : VectorSpace K V) {x y z : V}
    (h : space.add x y = space.add x z) : y = z := by
  let nx := vectorNeg space x
  have hnx : space.add x nx = space.zero := vectorNeg_spec space x
  have hnx' : space.add nx x = space.zero :=
    (space.add_comm nx x).trans hnx
  calc
    y = space.add space.zero y := (space.zero_add y).symm
    _ = space.add (space.add nx x) y := congrArg (fun t => space.add t y) hnx'.symm
    _ = space.add nx (space.add x y) := space.add_assoc nx x y
    _ = space.add nx (space.add x z) := congrArg (space.add nx) h
    _ = space.add (space.add nx x) z := (space.add_assoc nx x z).symm
    _ = space.add space.zero z := congrArg (fun t => space.add t z) hnx'
    _ = z := space.zero_add z

theorem smul_zero (space : VectorSpace K V) (a : K) :
    space.smul a space.zero = space.zero := by
  let q := space.smul a space.zero
  have hzero : space.add space.zero space.zero = space.zero :=
    space.zero_add space.zero
  have hq : space.add q q = q := by
    calc
      space.add q q = space.smul a (space.add space.zero space.zero) :=
        (space.smul_add a space.zero space.zero).symm
      _ = space.smul a space.zero := congrArg (space.smul a) hzero
      _ = q := rfl
  have hq0 : space.add q space.zero = q :=
    (space.add_comm q space.zero).trans (space.zero_add q)
  exact add_left_cancel space (hq.trans hq0.symm)

structure LinearMap (source : VectorSpace K V) (target : VectorSpace K W) where
  field_eq : source.field = target.field
  toFun : V → W
  map_add : ∀ x y, toFun (source.add x y) = target.add (toFun x) (toFun y)
  map_smul : ∀ a x, toFun (source.smul a x) = target.smul a (toFun x)

theorem linearMap_sends_zero {K : Type u} {V : Type v} {W : Type w}
    {source : VectorSpace K V} {target : VectorSpace K W}
    (T : LinearMap source target) :
    T.toFun source.zero = target.zero := by
  have hs : source.add source.zero source.zero = source.zero :=
    source.zero_add source.zero
  have hadd : target.add (T.toFun source.zero) (T.toFun source.zero) =
      T.toFun source.zero := by
    calc
      target.add (T.toFun source.zero) (T.toFun source.zero) =
          T.toFun (source.add source.zero source.zero) := (T.map_add _ _).symm
      _ = T.toFun source.zero := congrArg T.toFun hs
  have hzero : target.add (T.toFun source.zero) target.zero =
      T.toFun source.zero :=
    (target.add_comm _ _).trans (target.zero_add _)
  exact add_left_cancel target (hadd.trans hzero.symm)

theorem linearMap_sends_neg {K : Type u} {V : Type v} {W : Type w}
    {source : VectorSpace K V} {target : VectorSpace K W}
    (T : LinearMap source target) (x : V) :
    T.toFun (vectorNeg source x) = vectorNeg target (T.toFun x) := by
  have hleft : target.add (T.toFun x) (T.toFun (vectorNeg source x)) =
      target.zero := by
    calc
      target.add (T.toFun x) (T.toFun (vectorNeg source x)) =
          T.toFun (source.add x (vectorNeg source x)) := (T.map_add _ _).symm
      _ = T.toFun source.zero := congrArg T.toFun (vectorNeg_spec source x)
      _ = target.zero := linearMap_sends_zero T
  have hright : target.add (T.toFun x) (vectorNeg target (T.toFun x)) =
      target.zero := vectorNeg_spec target (T.toFun x)
  exact add_left_cancel target (hleft.trans hright.symm)

def Kernel {K : Type u} {V : Type v} {W : Type w}
    {source : VectorSpace K V} {target : VectorSpace K W}
    (T : LinearMap source target) : V → Prop :=
  fun x => T.toFun x = target.zero

def ZeroSubspace (space : VectorSpace K V) : V → Prop :=
  fun x => x = space.zero

structure Subspace (space : VectorSpace K V) where
  carrier : V → Prop
  zero_mem : carrier space.zero
  add_mem : ∀ {x y}, carrier x → carrier y → carrier (space.add x y)
  smul_mem : ∀ a {x}, carrier x → carrier (space.smul a x)

def kernelSubspace {K : Type u} {V : Type v} {W : Type w}
    {source : VectorSpace K V} {target : VectorSpace K W}
    (T : LinearMap source target) : Subspace source where
  carrier := Kernel T
  zero_mem := linearMap_sends_zero T
  add_mem := by
    intro x y hx hy
    change T.toFun x = target.zero at hx
    change T.toFun y = target.zero at hy
    calc
      T.toFun (source.add x y) = target.add (T.toFun x) (T.toFun y) := T.map_add x y
      _ = target.add target.zero target.zero := congrArg2 target.add hx hy
      _ = target.zero := target.zero_add target.zero
  smul_mem := by
    intro a x hx
    change T.toFun x = target.zero at hx
    calc
      T.toFun (source.smul a x) = target.smul a (T.toFun x) := T.map_smul a x
      _ = target.smul a target.zero := congrArg (target.smul a) hx
      _ = target.zero := smul_zero target a

def IsInjective {K : Type u} {V : Type v} {W : Type w}
    {source : VectorSpace K V} {target : VectorSpace K W}
    (T : LinearMap source target) : Prop :=
  ∀ x y, T.toFun x = T.toFun y → x = y

theorem injective_linear_map_has_trivial_kernel
    {K : Type u} {V : Type v} {W : Type w}
    {source : VectorSpace K V} {target : VectorSpace K W}
    (T : LinearMap source target) (hinjective : IsInjective T) :
    ∀ x, Kernel T x ↔ ZeroSubspace source x := by
  intro x
  constructor
  · intro hx
    exact hinjective x source.zero (hx.trans (linearMap_sends_zero T).symm)
  · intro hx
    exact hx ▸ linearMap_sends_zero T

theorem trivial_kernel_implies_injective
    {K : Type u} {V : Type v} {W : Type w}
    {source : VectorSpace K V} {target : VectorSpace K W}
    (T : LinearMap source target)
    (htrivial : ∀ x, Kernel T x ↔ ZeroSubspace source x) :
    IsInjective T := by
  intro x y hxy
  have hkernel : Kernel T (vectorSub source x y) := by
    change T.toFun (source.add x (vectorNeg source y)) = target.zero
    calc
      T.toFun (source.add x (vectorNeg source y)) =
          target.add (T.toFun x) (T.toFun (vectorNeg source y)) := T.map_add _ _
      _ = target.add (T.toFun x) (vectorNeg target (T.toFun y)) :=
          congrArg (target.add (T.toFun x)) (linearMap_sends_neg T y)
      _ = target.add (T.toFun y) (vectorNeg target (T.toFun y)) :=
          congrArg (fun t => target.add t (vectorNeg target (T.toFun y))) hxy
      _ = target.zero := vectorNeg_spec target (T.toFun y)
  have hsub : vectorSub source x y = source.zero :=
    (htrivial (vectorSub source x y)).mp hkernel
  have hleft : source.add (vectorNeg source y) x = source.zero :=
    (source.add_comm (vectorNeg source y) x).trans hsub
  have hright : source.add (vectorNeg source y) y = source.zero :=
    (source.add_comm (vectorNeg source y) y).trans (vectorNeg_spec source y)
  exact add_left_cancel source (hleft.trans hright.symm)

def coordinatePlane (field : Field K) : VectorSpace K (K × K) where
  field := field
  zero := (field.zero, field.zero)
  add x y := (field.add x.1 y.1, field.add x.2 y.2)
  smul a x := (field.mul a x.1, field.mul a x.2)
  add_assoc := by intro x y z; apply Prod.ext <;> exact field.add_assoc _ _ _
  add_comm := by intro x y; apply Prod.ext <;> exact field.add_comm _ _
  zero_add := by intro x; apply Prod.ext <;> exact field.zero_add _
  neg_exists := by
    intro x
    exact ⟨(field.neg x.1, field.neg x.2), by
      apply Prod.ext <;> exact field.add_neg _⟩
  smul_mul := by intro a b x; apply Prod.ext <;> exact field.mul_assoc _ _ _
  add_smul := by
    intro a b x
    apply Prod.ext
    · calc
        field.mul (field.add a b) x.1 = field.mul x.1 (field.add a b) := field.mul_comm _ _
        _ = field.add (field.mul x.1 a) (field.mul x.1 b) := field.mul_add _ _ _
        _ = field.add (field.mul a x.1) (field.mul b x.1) :=
          congrArg2 field.add (field.mul_comm _ _) (field.mul_comm _ _)
    · calc
        field.mul (field.add a b) x.2 = field.mul x.2 (field.add a b) := field.mul_comm _ _
        _ = field.add (field.mul x.2 a) (field.mul x.2 b) := field.mul_add _ _ _
        _ = field.add (field.mul a x.2) (field.mul b x.2) :=
          congrArg2 field.add (field.mul_comm _ _) (field.mul_comm _ _)
  smul_add := by intro a x y; apply Prod.ext <;> exact field.mul_add _ _ _
  one_smul := by intro x; apply Prod.ext <;> exact field.one_mul _

def projectionXAxis (field : Field K) :
    LinearMap (coordinatePlane field) (coordinatePlane field) where
  field_eq := rfl
  toFun x := (x.1, field.zero)
  map_add := by
    intro x y
    apply Prod.ext
    · rfl
    · exact (field.zero_add field.zero).symm
  map_smul := by
    intro a x
    have hz := smul_zero (coordinatePlane field) a
    have hcoord : field.mul a field.zero = field.zero := congrArg Prod.fst hz
    apply Prod.ext
    · rfl
    · exact hcoord.symm

theorem projection_x_axis_is_not_injective (field : Field K) :
    ¬ IsInjective (projectionXAxis field) := by
  intro hinjective
  have hpairs : (field.zero, field.one) = (field.zero, field.zero) :=
    hinjective _ _ rfl
  have hone_zero : field.one = field.zero := congrArg Prod.snd hpairs
  exact field.zero_ne_one hone_zero.symm

theorem projection_kernel_is_nontrivial (field : Field K) :
    Kernel (projectionXAxis field) (field.zero, field.one) := rfl

end LinearAlgebraSameMathInLean
