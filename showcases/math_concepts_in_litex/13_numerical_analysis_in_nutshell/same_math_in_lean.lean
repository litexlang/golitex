/- The same Newton-update and residual semantics as the Litex example.
Prelude has no rational/real field-normalization tactic, so the expanded
algebraic identity is an explicit setting boundary.  The public theorem then
folds that lower-level fact through the named residual interface. -/

structure NewtonOps where
  Scalar : Type
  zero : Scalar
  one : Scalar
  two : Scalar
  four : Scalar
  add : Scalar → Scalar → Scalar
  mul : Scalar → Scalar → Scalar
  div : Scalar → Scalar → Scalar
  sub : Scalar → Scalar → Scalar

def newtonUpdate (O : NewtonOps) (x : O.Scalar) : O.Scalar :=
  O.div (O.add x (O.div O.two x)) O.two

def residual (O : NewtonOps) (x : O.Scalar) : O.Scalar :=
  O.sub (O.mul x x) O.two

def ExpandedResidualIdentity (O : NewtonOps) : Prop :=
  ∀ x, x ≠ O.zero →
    O.mul (O.mul O.four (O.mul x x))
        (O.sub (O.mul (newtonUpdate O x) (newtonUpdate O x)) O.two) =
      O.mul (O.sub (O.mul x x) O.two) (O.sub (O.mul x x) O.two)

structure NewtonSqrtTwoSetting where
  ops : NewtonOps
  expandedResidualIdentity : ExpandedResidualIdentity ops

theorem newtonSqrtTwoResidualIdentity (S : NewtonSqrtTwoSetting)
    (x : S.ops.Scalar) (nonzero : x ≠ S.ops.zero) :
    S.ops.mul (S.ops.mul S.ops.four (S.ops.mul x x))
        (residual S.ops (newtonUpdate S.ops x)) =
      S.ops.mul (residual S.ops x) (residual S.ops x) := by
  simpa only [residual] using S.expandedResidualIdentity x nonzero
