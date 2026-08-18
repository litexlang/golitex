/- Prelude has no real derivative.  HasDerivative and the derivative of
x^2+1 are therefore explicit fields of the setting; the ODE connection and
initial value are proved without an axiom or proof hole. -/

structure DerivativeSetting where
  HasDerivative : (Int → Int) → Int → Int → Prop
  squarePlusOneDerivative :
    ∀ x, HasDerivative (fun t => t * t + 1) x (2 * x)

def odeRhs (x _y : Int) : Int := 2 * x
def odeSolution (x : Int) : Int := x * x + 1

def SolvesAt (S : DerivativeSetting) (f : Int → Int)
    (rhs : Int → Int → Int) (x : Int) : Prop :=
  ∃ slope, S.HasDerivative f x slope ∧ slope = rhs x (f x)

theorem squarePlusOneSolves (S : DerivativeSetting) (x : Int) :
    SolvesAt S odeSolution odeRhs x := by
  refine ⟨2 * x, ?_, rfl⟩
  exact S.squarePlusOneDerivative x

example : odeSolution 0 = 1 := rfl
