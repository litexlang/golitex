import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_sign_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}

noncomputable def _object_w1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
(Litex.sign _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (3 : ℂ)) (-3 : ℝ) (by norm_num))))))

noncomputable def _object_w2 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  let _equal_wd_1_1 := (_object_w2 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        let _equal_wd_1_1 := (_object_w2 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (-1 : ℂ) (- (1 : ℂ)) (let _sign := _equal_wd_1_0;
        let _member : Litex.In _sign Litex.C := Litex.integerToComplex _sign (Litex.signInZ _sign);
        (Litex.signDenoteReal _sign (-3 : ℝ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_equal_wd_1_0).val.arg).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = (((-3 : ℝ) : ℝ) : ℂ))))).trans (congrArg M.number (by norm_num [Real.sign] : ((Real.sign (-3 : ℝ) : ℝ) : ℂ) = (-1 : ℂ)))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num))))
      )
  )

noncomputable def _object_w3 := (Litex.sign (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))

theorem h_7 : (by
  let _equal_wd_1_0 := (_object_w3 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (0 : ℂ) (let _sign := _equal_wd_1_0;
        let _member : Litex.In _sign Litex.C := Litex.integerToComplex _sign (Litex.signInZ _sign);
        (Litex.signDenoteReal _sign (0 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (((0 : ℝ) : ℝ) : ℂ))))).trans (congrArg M.number (by norm_num [Real.sign] : ((Real.sign (0 : ℝ) : ℝ) : ℂ) = (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w5 := (Litex.sign (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)))

theorem h_10 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (let _sign := _equal_wd_1_0;
        let _member : Litex.In _sign Litex.C := Litex.integerToComplex _sign (Litex.signInZ _sign);
        (Litex.signDenoteReal _sign (4 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (((4 : ℝ) : ℝ) : ℂ))))).trans (congrArg M.number (by norm_num [Real.sign] : ((Real.sign (4 : ℝ) : ℝ) : ℂ) = (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w7 := (let _wd_1_0 := (let _wd_2_0 := ((_object_w1 (M := M))).val.arg;
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
(Litex.sign _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((- (3 : ℂ)) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_atomic_wd_1_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((- (3 : ℂ)) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num))))))

theorem h_13 : (by
  let _equal_wd_1_0 := (_object_w7 (M := M))
  let _equal_wd_1_1 := (_object_w2 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w7 (M := M));
        let _equal_wd_1_1 := (_object_w2 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (-1 : ℂ) (- (1 : ℂ)) (let _sign := _equal_wd_1_0;
        let _member : Litex.In _sign Litex.C := Litex.integerToComplex _sign (Litex.signInZ _sign);
        (Litex.signDenoteReal _sign ((-3 : ℝ) / (2 : ℝ)) (((Litex.NativeBridge.denoteDiv ((_equal_wd_1_0).val.arg).val.left (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (((_equal_wd_1_0).val.arg).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((- (3 : ℂ)) / (2 : ℂ)) = ((((-3 : ℝ) / (2 : ℝ)) : ℝ) : ℂ))))).trans (congrArg M.number (by norm_num [Real.sign] : ((Real.sign ((-3 : ℝ) / (2 : ℝ)) : ℝ) : ℂ) = (-1 : ℂ)))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_object_w2 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num))))
      )
  )

theorem h_30 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_43 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w9 := (Litex.sign _value_i1 h_43)
  exact (((by
    let _atomic_wd_1_0 := _object_w9
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w9
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w9
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w9
    exact Litex.IsSet _atomic_wd_1_0)))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_43
          let _object_w9 := (Litex.sign _value_i1 h_43)
          have h_26 : (by
            let _atomic_wd_1_0 := _object_w9
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    exact (Litex.signInZ _atomic_wd_1_0))
                )
            )
          have h_27 : (by
            let _atomic_wd_1_0 := _object_w9
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    exact (Litex.integerToReal _atomic_wd_1_0 h_26))
                )
            )
          have h_28 : (by
            let _atomic_wd_1_0 := _object_w9
            exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    exact (M.real_subset_complex _ h_27))
                )
            )
          have h_29 : (by
            let _atomic_wd_1_0 := _object_w9
            exact Litex.IsSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    exact (Litex.isSet _atomic_wd_1_0))
                )
            )
          exact (And.intro h_26 (And.intro h_27 (And.intro h_28 h_29)))
        )
      )
  )

theorem h_93 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_106 : Litex.In _value_i2 (Litex.R (M := M))) (h_91 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2), (by
  let _object_w13 := (Litex.sign _value_i2 h_106)
  exact (by
    let _equal_wd_1_0 := _object_w13
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_106 h_91
          let _object_w13 := (Litex.sign _value_i2 h_106)
          have h_92 : (by
            let _equal_wd_1_0 := _object_w13
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w13;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from ((Litex.signOfPositive _equal_wd_1_0 h_91).trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))).symm)))
                )
            )
          exact h_92
        )
      )
  )

theorem h_129 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_143 : Litex.In _value_i3 (Litex.R (M := M))) (h_127 : Litex.Lt _value_i3 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w15 := (Litex.sign _value_i3 h_143)
  let _object_w16 := (Litex.sub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
  exact (by
    let _equal_wd_1_0 := _object_w15
    let _equal_wd_1_1 := _object_w16
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_143 h_127
          let _object_w15 := (Litex.sign _value_i3 h_143)
          let _object_w16 := (Litex.sub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
          have h_128 : (by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w15;
                  let _equal_wd_1_1 := _object_w16;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((Litex.signOfNegative _equal_wd_1_0 h_127).trans (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = ((-1) : ℂ)))).symm)))
                )
            )
          exact h_128
        )
      )
  )

theorem h_181 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_197 : Litex.In _value_i4 (Litex.R (M := M))) (h_179 : Litex.Lt _value_i4 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w18 := (Litex.sign _value_i4 h_197)
  exact (by
    let _equal_wd_1_0 := (_object_w2 (M := M))
    let _equal_wd_1_1 := _object_w18
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_197 h_179
          let _object_w18 := (Litex.sign _value_i4 h_197)
          have h_180 : (by
            let _equal_wd_1_0 := (_object_w2 (M := M))
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := (_object_w2 (M := M));
                  let _equal_wd_1_1 := _object_w18;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((Litex.signOfNegative _equal_wd_1_1 h_179).trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_object_w2 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = ((-1) : ℂ)))).symm).symm))
                )
            )
          exact h_180
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_sign_x2f_statement_x2e_lit
