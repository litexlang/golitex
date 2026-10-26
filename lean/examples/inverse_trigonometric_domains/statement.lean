import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_inverse_x5f_trigonometric_x5f_domains_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w2 := (Litex.arctan _value_i1 h_19)
  have h_1 : (by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := _object_w2
            exact (Litex.arctanInR _atomic_wd_1_0))
        )
    )
  let _object_w3 := (Litex.arccot _value_i1 h_19)
  have h_2 : (by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := _object_w3
            exact (Litex.arccotInR _atomic_wd_1_0))
        )
    )
  let _object_w4 := (let _wd_1_0 := _object_w2;
  (let _inverse := _wd_1_0; Litex.sec _inverse (by
    let _atomic_wd_1_0 := _object_w2
    exact h_1) (Litex.cosArctanNonzero _inverse)))
  let _object_w5 := (let _wd_1_0 := _object_w3;
  (let _inverse := _wd_1_0; Litex.csc _inverse (by
    let _atomic_wd_1_0 := _object_w3
    exact h_2) (Litex.sinArccotNonzero _inverse)))
  let _object_w6 := (let _wd_1_0 := _object_w2;
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _object_w2
    exact (M.real_subset_complex _ h_1)) (Litex.numberInC (M := M) (0 : ℂ))))
  exact (((by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w4
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w5
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((by
    let _equal_wd_1_0 := _object_w6
    let _equal_wd_1_1 := _object_w2
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_19
          let _object_w2 := (Litex.arctan _value_i1 h_19)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.arctanInR _atomic_wd_1_0))
                )
            )
          let _object_w3 := (Litex.arccot _value_i1 h_19)
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w3
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact (Litex.arccotInR _atomic_wd_1_0))
                )
            )
          let _object_w4 := (let _wd_1_0 := _object_w2;
          (let _inverse := _wd_1_0; Litex.sec _inverse (by
            let _atomic_wd_1_0 := _object_w2
            exact h_1) (Litex.cosArctanNonzero _inverse)))
          have h_3 : (by
            let _atomic_wd_1_0 := _object_w4
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w4
                    exact (Litex.inRStar_base _atomic_wd_1_0 (Litex.secInRStar _atomic_wd_1_0)))
                )
            )
          let _object_w5 := (let _wd_1_0 := _object_w3;
          (let _inverse := _wd_1_0; Litex.csc _inverse (by
            let _atomic_wd_1_0 := _object_w3
            exact h_2) (Litex.sinArccotNonzero _inverse)))
          have h_4 : (by
            let _atomic_wd_1_0 := _object_w5
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    exact (Litex.inRStar_base _atomic_wd_1_0 (Litex.cscInRStar _atomic_wd_1_0)))
                )
            )
          let _object_w6 := (let _wd_1_0 := _object_w2;
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w2
            exact (M.real_subset_complex _ h_1)) (Litex.numberInC (M := M) (0 : ℂ))))
          have h_5 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w2
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w6;
                  let _equal_wd_1_1 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Real.arctan ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re : ℂ) + (0 : ℂ)) (Real.arctan ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re : ℂ) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _trig := _object_w2; Litex.denoteArctan _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19)) _trig.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_19)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (let _trig := _object_w2; Litex.denoteArctan _trig ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19)) _trig.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_19)))) (by ring!))))
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 (And.intro h_4 h_5))))
        )
      )
  )

theorem h_130 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_143 : Litex.In _value_i2 (Litex.R (M := M))) (h_126 : (by
  let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
  exact Litex.Le _atomic_wd_1_0 _value_i2)) (h_127 : Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ))), (by
  let _object_w10 := (Litex.arcsin _value_i2 h_143 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i2 _value_i2 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_126) h_127)
  let _object_w11 := (Litex.arccos _value_i2 h_143 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i2 _value_i2 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_126) h_127)
  exact (((by
    let _atomic_wd_1_0 := _object_w10
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w11
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_143 h_126 h_127
          let _object_w10 := (Litex.arcsin _value_i2 h_143 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i2 _value_i2 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_126) h_127)
          have h_128 : (by
            let _atomic_wd_1_0 := _object_w10
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w10
                    exact (Litex.arcsinInR _atomic_wd_1_0))
                )
            )
          let _object_w11 := (Litex.arccos _value_i2 h_143 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i2 _value_i2 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_126) h_127)
          have h_129 : (by
            let _atomic_wd_1_0 := _object_w11
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w11
                    exact (Litex.arccosInR _atomic_wd_1_0))
                )
            )
          exact (And.intro h_128 h_129)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_inverse_x5f_trigonometric_x5f_domains_x2f_statement_x2e_lit
