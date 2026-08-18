/- The same algebraic content as the Litex Bayes example.  Positivity and
probability-measure infrastructure are library boundaries absent from Prelude;
the denominator guard therefore remains an explicit premise. -/

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
