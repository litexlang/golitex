/-
The same mathematics as `main.lit`, expressed in pure Lean 4.

`Int` and its elementary ring laws are part of Lean's Prelude, so this file
needs no import. It is handwritten comparison code, not compiler output.
-/

namespace NumberTheorySameMathInLean

theorem congrArg2 {X Y : Type} {Z : Sort _} (f : X → Y → Z)
    {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    f x₁ y₁ = f x₂ y₂ := by
  cases hx
  cases hy
  rfl

def DividesBy (d n : Int) : Prop := ∃ k, n = d * k

theorem divisibility_is_transitive {a b c : Int}
    (hab : DividesBy a b) (hbc : DividesBy b c) : DividesBy a c := by
  cases hab with
  | intro k hk =>
      cases hbc with
      | intro m hm =>
          refine ⟨k * m, ?_⟩
          calc
            c = b * m := hm
            _ = (a * k) * m := congrArg (fun value => value * m) hk
            _ = a * (k * m) := Int.mul_assoc a k m

theorem common_divisor_divides_linear_combination
    {d a b x y : Int} (hda : DividesBy d a) (hdb : DividesBy d b) :
    DividesBy d (a * x + b * y) := by
  cases hda with
  | intro p hp =>
      cases hdb with
      | intro q hq =>
          refine ⟨p * x + q * y, ?_⟩
          calc
            a * x + b * y = (d * p) * x + (d * q) * y :=
              congrArg2 (fun left right => left * x + right * y) hp hq
            _ = d * (p * x) + d * (q * y) :=
              congrArg2 (· + ·) (Int.mul_assoc d p x) (Int.mul_assoc d q y)
            _ = d * (p * x + q * y) := (Int.mul_add d (p * x) (q * y)).symm

structure GcdCertificate (a b d : Int) : Prop where
  positive : d > 0
  divides_left : DividesBy d a
  divides_right : DividesBy d b
  greatest : ∀ common, common > 0 → DividesBy common a →
    DividesBy common b → DividesBy common d
  bezout : ∃ x y, d = a * x + b * y

def LinearDiophantineSoluble (a b c : Int) : Prop :=
  ∃ x y, a * x + b * y = c

theorem diophantine_solution_implies_gcd_divides_target
    {a b c d : Int} (certificate : GcdCertificate a b d)
    (solution : LinearDiophantineSoluble a b c) : DividesBy d c := by
  cases solution with
  | intro x rest =>
      cases rest with
      | intro y equation =>
          have combination_divisible : DividesBy d (a * x + b * y) :=
            common_divisor_divides_linear_combination
              certificate.divides_left certificate.divides_right
          cases combination_divisible with
          | intro k hk => exact ⟨k, equation ▸ hk⟩

theorem gcd_divides_target_implies_diophantine_solution
    {a b c d : Int} (certificate : GcdCertificate a b d)
    (target_divisible : DividesBy d c) : LinearDiophantineSoluble a b c := by
  cases certificate.bezout with
  | intro u rest =>
      cases rest with
      | intro v bezout =>
          cases target_divisible with
          | intro k hc =>
              refine ⟨u * k, v * k, ?_⟩
              calc
                a * (u * k) + b * (v * k) = (a * u) * k + (b * v) * k :=
                  congrArg2 (· + ·) (Int.mul_assoc a u k).symm
                    (Int.mul_assoc b v k).symm
                _ = (a * u + b * v) * k := (Int.add_mul (a * u) (b * v) k).symm
                _ = d * k := congrArg (fun value => value * k) bezout.symm
                _ = c := hc.symm

def CongruentMod (a b modulus : Int) : Prop :=
  modulus > 0 ∧ DividesBy modulus (a - b)

theorem congruence_is_compatible_with_addition
    {a b c d modulus : Int}
    (hab : CongruentMod a b modulus) (hcd : CongruentMod c d modulus) :
    CongruentMod (a + c) (b + d) modulus := by
  refine ⟨hab.left, ?_⟩
  cases hab.right with
  | intro k hk =>
      cases hcd.right with
      | intro m hm =>
          refine ⟨k + m, ?_⟩
          calc
            (a + c) - (b + d) = (a - b) + (c - d) := by
              simp only [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc,
                Int.add_left_comm]
            _ = modulus * k + modulus * m :=
              congrArg2 (· + ·) hk hm
            _ = modulus * (k + m) := (Int.mul_add modulus k m).symm

example : DividesBy 3 60 := by
  exact divisibility_is_transitive (a := 3) (b := 12) (c := 60)
    ⟨4, by decide⟩ ⟨5, by decide⟩

end NumberTheorySameMathInLean
