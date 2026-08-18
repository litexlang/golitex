import Mathlib

/- The same two-point real probability calculations as `main.lit`.
Probabilities, expectations, variance, and conditional probability all remain
real-valued rather than being replaced by integer arithmetic. -/

namespace ProbabilityAndStatisticsSameMathInLean

noncomputable section

abbrev Pair := ℝ × ℝ

def IsProbabilityVector2 (p : Pair) : Prop :=
  0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1

def expectation2 (values probs : Pair) : ℝ :=
  values.1 * probs.1 + values.2 * probs.2

def variance2 (values probs : Pair) : ℝ :=
  (values.1 - expectation2 values probs) ^ 2 * probs.1 +
    (values.2 - expectation2 values probs) ^ 2 * probs.2

def affineCombine2 (X Y : Pair) (a b : ℝ) : Pair :=
  (a * X.1 + b * Y.1, a * X.2 + b * Y.2)

theorem expectation2Affine (X Y probs : Pair) (a b : ℝ) :
    expectation2 (affineCombine2 X Y a b) probs =
      a * expectation2 X probs + b * expectation2 Y probs := by
  simp [expectation2, affineCombine2]
  ring

def fairCoinValues : Pair := (0, 1)
def fairCoinProbs : Pair := (1 / 2, 1 / 2)

example : IsProbabilityVector2 fairCoinProbs := by
  norm_num [IsProbabilityVector2, fairCoinProbs]

example : expectation2 fairCoinValues fairCoinProbs = 1 / 2 := by
  norm_num [expectation2, fairCoinValues, fairCoinProbs]

example : variance2 fairCoinValues fairCoinProbs = 1 / 4 := by
  norm_num [variance2, expectation2, fairCoinValues, fairCoinProbs]

def conditionalProbability (joint evidence : ℝ) : ℝ := joint / evidence
def bayesPosterior (prior likelihood evidence : ℝ) : ℝ :=
  likelihood * prior / evidence

theorem bayesRule {prior likelihood evidence joint : ℝ}
    (_evidencePositive : 0 < evidence)
    (jointEq : joint = likelihood * prior) :
    conditionalProbability joint evidence =
      bayesPosterior prior likelihood evidence := by
  simp [conditionalProbability, bayesPosterior, jointEq]

example : conditionalProbability (1 / 4) (1 / 2) = 1 / 2 := by
  norm_num [conditionalProbability]

end

end ProbabilityAndStatisticsSameMathInLean
