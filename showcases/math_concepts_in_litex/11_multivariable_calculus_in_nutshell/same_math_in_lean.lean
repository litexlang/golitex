/- Prelude-level representation of the Litex quadratic surface example.
The polynomial difference identity is proved directly.  Since Prelude has no
real numbers or multivariable derivative library, only the two coordinate
partial-derivative facts remain explicit setting boundaries. -/

structure Point where
  x : Int
  y : Int
deriving DecidableEq

def quadraticSurface (p : Point) : Int :=
  p.x * p.x + p.y * p.y

def quadraticGradient (p : Point) : Point :=
  { x := 2 * p.x, y := 2 * p.y }

theorem squareDifference (x y : Int) :
    x * x - y * y = (x - y) * (x + y) := by
  rw [Int.sub_mul, Int.mul_add, Int.mul_add]
  rw [Int.mul_comm y x]
  omega

theorem coordinateDifferenceIdentity
    (p : Point) (x : Int) :
    quadraticSurface { x := x, y := p.y } - quadraticSurface p =
      (x - p.x) * (x + p.x) := by
  simp only [quadraticSurface]
  rw [Int.add_sub_add_right]
  exact squareDifference x p.x

structure PartialDerivativeSetting where
  HasXPartial : (Point → Int) → Point → Int → Prop
  HasYPartial : (Point → Int) → Point → Int → Prop
  quadraticX : ∀ p, HasXPartial quadraticSurface p (2 * p.x)
  quadraticY : ∀ p, HasYPartial quadraticSurface p (2 * p.y)

def IsCoordinateGradient (S : PartialDerivativeSetting)
    (f : Point → Int) (p gradient : Point) : Prop :=
  S.HasXPartial f p gradient.x ∧ S.HasYPartial f p gradient.y

theorem quadraticGradientIsCoordinateGradient
    (S : PartialDerivativeSetting) (p : Point) :
    IsCoordinateGradient S quadraticSurface p (quadraticGradient p) := by
  constructor
  · exact S.quadraticX p
  · exact S.quadraticY p

example : quadraticGradient { x := 3, y := 4 } = { x := 6, y := 8 } := by
  decide
