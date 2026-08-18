/- Prelude has no real derivative.  HasDerivative and the derivative law for
the quadratic family are therefore explicit fields of the setting.  The fixed
ODE solution and the initial-value parameter are derived from that interface. -/

def quadraticSolution (c x : Int) : Int := x * x + c
def odeSolution (x : Int) : Int := quadraticSolution 1 x
def odeRhs (x _y : Int) : Int := 2 * x

structure DerivativeSetting where
  HasDerivative : (Int → Int) → Int → Int → Prop
  quadraticDerivative :
    ∀ c x, HasDerivative (quadraticSolution c) x (2 * x)

def SolvesAt (S : DerivativeSetting) (f : Int → Int)
    (rhs : Int → Int → Int) (x : Int) : Prop :=
  ∃ slope, S.HasDerivative f x slope ∧ slope = rhs x (f x)

theorem quadraticInitialValueSelectsParameter (c y₀ : Int)
    (initialValue : quadraticSolution c 0 = y₀) : c = y₀ := by
  simpa [quadraticSolution] using initialValue

theorem odeSolutionHasDerivative (S : DerivativeSetting) (x : Int) :
    S.HasDerivative odeSolution x (2 * x) := by
  change S.HasDerivative (quadraticSolution 1) x (2 * x)
  exact S.quadraticDerivative 1 x

theorem odeSolutionSolvesEquation (S : DerivativeSetting) (x : Int) :
    SolvesAt S odeSolution odeRhs x := by
  refine ⟨2 * x, ?_, rfl⟩
  exact odeSolutionHasDerivative S x

example : odeSolution 0 = 1 := rfl
