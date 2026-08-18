/- The same finite-expectation and Bayes semantics as the Litex example,
using only Lean's automatically loaded Prelude.  Integer-valued pairs suffice
to prove the algebraic linearity law without importing an algebra library. -/

structure Pair where
  first : Int
  second : Int

def affineCombine2 (X Y : Pair) (a b : Int) : Pair :=
  { first := a * X.first + b * Y.first
    second := a * X.second + b * Y.second }

def expectation2 (values probs : Pair) : Int :=
  values.first * probs.first + values.second * probs.second

theorem expectation2Affine (X Y probs : Pair) (a b : Int) :
    expectation2 (affineCombine2 X Y a b) probs =
      a * expectation2 X probs + b * expectation2 Y probs := by
  simp only [expectation2, affineCombine2, Int.add_mul, Int.mul_add,
    Int.mul_assoc]
  ac_rfl

/- Positivity and probability-measure infrastructure are library boundaries
absent from Prelude; the denominator guard therefore remains explicit. -/

def conditionalProbability [Div α] (joint evidence : α) : α :=
  joint / evidence

def bayesPosterior [Mul α] [Div α]
    (prior likelihood evidence : α) : α :=
  likelihood * prior / evidence

theorem bayesRule [Mul α] [Div α]
    (prior likelihood evidence joint zero : α)
    (_evidenceNonzero : evidence ≠ zero)
    (jointEq : joint = likelihood * prior) :
    conditionalProbability joint evidence =
      bayesPosterior prior likelihood evidence := by
  unfold conditionalProbability bayesPosterior
  rw [jointEq]
