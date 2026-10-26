import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_inverse_x5f_trigonometric_x5f_left_x5f_inverses_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w2 := (let _wd_1_0 := (Litex.arctan _value_i1 h_16);
  (let _inverse := _wd_1_0; Litex.tan _inverse (by
    let _atomic_wd_1_0 := (Litex.arctan _value_i1 h_16)
    exact (Litex.arctanInR _atomic_wd_1_0)) (Litex.cosArctanNonzero _inverse)))
  let _object_w3 := (let _wd_1_0 := (Litex.arccot _value_i1 h_16);
  (let _inverse := _wd_1_0; Litex.cot _inverse (by
    let _atomic_wd_1_0 := (Litex.arccot _value_i1 h_16)
    exact (Litex.arccotInR _atomic_wd_1_0)) (Litex.sinArccotNonzero _inverse)))
  exact (((by
    let _equal_wd_1_0 := _object_w2
    exact Litex.Same _equal_wd_1_0 _value_i1)) ∧ ((by
    let _equal_wd_1_0 := _object_w3
    exact Litex.Same _equal_wd_1_0 _value_i1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16
          let _object_w2 := (let _wd_1_0 := (Litex.arctan _value_i1 h_16);
          (let _inverse := _wd_1_0; Litex.tan _inverse (by
            let _atomic_wd_1_0 := (Litex.arctan _value_i1 h_16)
            exact (Litex.arctanInR _atomic_wd_1_0)) (Litex.cosArctanNonzero _inverse)))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (Litex.tanArctan (_equal_wd_1_0).val.arg)))
                )
            )
          let _object_w3 := (let _wd_1_0 := (Litex.arccot _value_i1 h_16);
          (let _inverse := _wd_1_0; Litex.cot _inverse (by
            let _atomic_wd_1_0 := (Litex.arccot _value_i1 h_16)
            exact (Litex.arccotInR _atomic_wd_1_0)) (Litex.sinArccotNonzero _inverse)))
          have h_2 : (by
            let _equal_wd_1_0 := _object_w3
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (Litex.cotArccot (_equal_wd_1_0).val.arg)))
                )
            )
          exact (And.intro h_1 h_2)
        )
      )
  )

theorem h_61 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_74 : Litex.In _value_i2 (Litex.R (M := M))) (h_57 : (by
  let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
  exact Litex.Le _atomic_wd_1_0 _value_i2)) (h_58 : Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ))), (by
  let _object_w7 := (let _wd_1_0 := (Litex.arcsin _value_i2 h_74 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i2 _value_i2 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_57) h_58);
  (Litex.sin _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.arcsin _value_i2 h_74 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i2 _value_i2 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_57) h_58)
    exact (Litex.arcsinInR _atomic_wd_1_0))))
  let _object_w8 := (let _wd_1_0 := (Litex.arccos _value_i2 h_74 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i2 _value_i2 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_57) h_58);
  (Litex.cos _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.arccos _value_i2 h_74 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i2 _value_i2 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_57) h_58)
    exact (Litex.arccosInR _atomic_wd_1_0))))
  exact (((by
    let _equal_wd_1_0 := _object_w7
    exact Litex.Same _equal_wd_1_0 _value_i2)) ∧ ((by
    let _equal_wd_1_0 := _object_w8
    exact Litex.Same _equal_wd_1_0 _value_i2)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_74 h_57 h_58
          let _object_w7 := (let _wd_1_0 := (Litex.arcsin _value_i2 h_74 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i2 _value_i2 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_57) h_58);
          (Litex.sin _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.arcsin _value_i2 h_74 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i2 _value_i2 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_57) h_58)
            exact (Litex.arcsinInR _atomic_wd_1_0))))
          have h_59 : (by
            let _equal_wd_1_0 := _object_w7
            exact Litex.Same _equal_wd_1_0 _value_i2) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w7;
                  (show Litex.Same _equal_wd_1_0 _value_i2 from (Litex.sinArcsin (_equal_wd_1_0).val.arg)))
                )
            )
          let _object_w8 := (let _wd_1_0 := (Litex.arccos _value_i2 h_74 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i2 _value_i2 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_57) h_58);
          (Litex.cos _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.arccos _value_i2 h_74 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i2 _value_i2 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_57) h_58)
            exact (Litex.arccosInR _atomic_wd_1_0))))
          have h_60 : (by
            let _equal_wd_1_0 := _object_w8
            exact Litex.Same _equal_wd_1_0 _value_i2) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w8;
                  (show Litex.Same _equal_wd_1_0 _value_i2 from (Litex.cosArccos (_equal_wd_1_0).val.arg)))
                )
            )
          exact (And.intro h_59 h_60)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_inverse_x5f_trigonometric_x5f_left_x5f_inverses_x2f_statement_x2e_lit
