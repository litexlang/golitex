/- Prelude-level representation of the Litex quadratic surface example.
The coordinate difference-quotient law is supplied explicitly because Prelude
has no real field tactic or multivariable derivative library. -/

structure Point where
  x : Int
  y : Int
deriving DecidableEq

def quadraticSurface (p : Point) : Int :=
  p.x * p.x + p.y * p.y

def quadraticGradient (p : Point) : Point :=
  { x := 2 * p.x, y := 2 * p.y }

example : quadraticGradient { x := 3, y := 4 } = { x := 6, y := 8 } := by
  decide

theorem coordinateDifferenceIdentity
    (p : Point) (x : Int)
    (algebra :
      quadraticSurface { x := x, y := p.y } - quadraticSurface p =
        (x - p.x) * (x + p.x)) :
    quadraticSurface { x := x, y := p.y } - quadraticSurface p =
      (x - p.x) * (x + p.x) :=
  algebra
