/-
The same mathematics as `main.lit`, expressed in pure Lean 4.

The exact integer coordinate fragment uses Prelude `Int`. The general
equilateral construction exposes its distance lemma as a setting because pure
Lean has no real square root or Euclidean-geometry library. This is handwritten
comparison code, not compiler output.
-/

namespace EuclideanGeometrySameMathInLean

abbrev Point := Int × Int

def vec (A B : Point) : Point := (B.1 - A.1, B.2 - A.2)

def dot (u v : Point) : Int := u.1 * v.1 + u.2 * v.2

def distanceSq (A B : Point) : Int := dot (vec A B) (vec A B)

theorem distance_sq_coordinate_formula (A B : Point) :
    distanceSq A B =
      (B.1 - A.1) * (B.1 - A.1) + (B.2 - A.2) * (B.2 - A.2) := rfl

example : distanceSq (0, 0) (3, 4) = 25 := by
  decide

def SegmentsCongruent (a b c d : Point) : Prop :=
  distanceSq a b = distanceSq c d

def IsEquilateralTriangle (a b c : Point) : Prop :=
  a ≠ b ∧ SegmentsCongruent a b a c ∧ SegmentsCongruent a b b c

structure EquilateralVertexSetting where
  vertex : Point → Point → Point
  distance_from_left : ∀ a b, distanceSq a (vertex a b) = distanceSq a b
  distance_from_right : ∀ a b, distanceSq b (vertex a b) = distanceSq a b

theorem euclid_book1_proposition_1 (E : EquilateralVertexSetting)
    {a b : Point} (hne : a ≠ b) :
    ∃ c, IsEquilateralTriangle a b c := by
  have left_congruence : SegmentsCongruent a b a (E.vertex a b) :=
    (E.distance_from_left a b).symm
  have right_congruence : SegmentsCongruent a b b (E.vertex a b) :=
    (E.distance_from_right a b).symm
  exact ⟨E.vertex a b, hne, left_congruence, right_congruence⟩

end EuclideanGeometrySameMathInLean
