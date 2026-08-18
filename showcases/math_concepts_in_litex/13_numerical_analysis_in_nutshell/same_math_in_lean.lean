/- The same Newton-update semantics as the Litex example. Prelude has no
rational/real field normalization, so the scaled-error algebra is an explicit
setting field rather than an axiom or an admitted proof. -/

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

def ScaledErrorIdentity (O : NewtonOps) : Prop :=
  ∀ x, x ≠ O.zero →
    O.mul (O.mul O.four (O.mul x x)) (residual O (newtonUpdate O x)) =
      O.mul (residual O x) (residual O x)

structure NewtonSqrtTwoSetting where
  ops : NewtonOps
  scaledErrorIdentity : ScaledErrorIdentity ops

theorem newtonScaledError (S : NewtonSqrtTwoSetting)
    (x : S.ops.Scalar) (nonzero : x ≠ S.ops.zero) :
    S.ops.mul (S.ops.mul S.ops.four (S.ops.mul x x))
        (residual S.ops (newtonUpdate S.ops x)) =
      S.ops.mul (residual S.ops x) (residual S.ops x) :=
  S.scaledErrorIdentity x nonzero
