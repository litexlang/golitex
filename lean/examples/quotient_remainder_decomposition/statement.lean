import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_quotient_x5f_remainder_x5f_decomposition_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_31 : Litex.In _value_i1 (Litex.Z (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_32 : Litex.In _value_i2 (Litex.NPos (M := M))), (by
  have h_33 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inNPos_positive _value_i2 h_32)
        )
    )
  have h_35 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_33) _litex_zero.symm)
        )
    )
  let _object_w4 := (Litex.quot _value_i1 _value_i2 h_31 h_32)
  have h_1 : (by
    let _atomic_wd_1_0 := _object_w4
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := _object_w4
            exact (Litex.quotInZ _atomic_wd_1_0))
        )
    )
  let _object_w5 := (Litex.mod _value_i1 _value_i2 h_31 (Litex.naturalToInteger _value_i2 (Litex.inNPos_natural _value_i2 h_32)) h_35)
  have h_2 : (by
    let _atomic_wd_1_0 := _object_w5
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := _object_w5
            exact (Litex.modInZ _atomic_wd_1_0))
        )
    )
  let _object_w6 := (let _wd_1_0 := (let _wd_2_0 := _value_i2;
  let _wd_2_1 := _object_w4;
  (Litex.mul _wd_2_0 _wd_2_1 (Litex.naturalToComplex _wd_2_0 (Litex.inNPos_natural _wd_2_0 h_32)) (by
    let _atomic_wd_1_0 := _object_w4
    exact (Litex.integerToComplex _atomic_wd_1_0 h_1))));
  let _wd_1_1 := _object_w5;
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC _value_i2 (_atomic_wd_1_0).val.right (Litex.naturalToComplex _value_i2 (Litex.inNPos_natural _value_i2 h_32)) (Litex.integerToComplex (_atomic_wd_1_0).val.right h_1))) (by
    let _atomic_wd_1_0 := _object_w5
    exact (Litex.integerToComplex _atomic_wd_1_0 h_2))))
  exact (((by
    let _atomic_wd_1_0 := _object_w4
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w5
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))) ∧ ((((by
    let _equal_wd_1_1 := _object_w6
    exact Litex.Same _value_i1 _equal_wd_1_1)) ∧ ((((by
    let _atomic_wd_1_1 := _object_w5
    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)) ∧ ((by
    let _atomic_wd_1_0 := _object_w5
    exact Litex.Lt _atomic_wd_1_0 _value_i2)))))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_31 _Host_i2 _rep_i2 _value_i2 h_32
          have h_33 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i2 h_32)
                )
            )
          have h_34 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_33)
                )
            )
          have h_35 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_33) _litex_zero.symm)
                )
            )
          let _object_w4 := (Litex.quot _value_i1 _value_i2 h_31 h_32)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w4
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w4
                    exact (Litex.quotInZ _atomic_wd_1_0))
                )
            )
          let _object_w5 := (Litex.mod _value_i1 _value_i2 h_31 (Litex.naturalToInteger _value_i2 (Litex.inNPos_natural _value_i2 h_32)) h_35)
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w5
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    exact (Litex.modInZ _atomic_wd_1_0))
                )
            )
          let _object_w6 := (let _wd_1_0 := (let _wd_2_0 := _value_i2;
          let _wd_2_1 := _object_w4;
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.naturalToComplex _wd_2_0 (Litex.inNPos_natural _wd_2_0 h_32)) (by
            let _atomic_wd_1_0 := _object_w4
            exact (Litex.integerToComplex _atomic_wd_1_0 h_1))));
          let _wd_1_1 := _object_w5;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInC _value_i2 (_atomic_wd_1_0).val.right (Litex.naturalToComplex _value_i2 (Litex.inNPos_natural _value_i2 h_32)) (Litex.integerToComplex (_atomic_wd_1_0).val.right h_1))) (by
            let _atomic_wd_1_0 := _object_w5
            exact (Litex.integerToComplex _atomic_wd_1_0 h_2))))
          have h_3 : (by
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _value_i1 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_1 := _object_w6;
                  (show Litex.Same _value_i1 _equal_wd_1_1 from (Litex.quotDecomposition ((_equal_wd_1_1).val.left).val.right false)))
                )
            )
          have h_4 : (by
            let _atomic_wd_1_1 := _object_w5
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w5
                    exact (Litex.modNonnegative _atomic_wd_1_1 h_31 h_32))
                )
            )
          have h_687 : Litex.In (_object_w6).val.right (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) (_object_w6).val.right (by
                    let _atomic_wd_1_0 := _object_w5
                    exact h_2) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_4)
                )
            )
          have h_5 : (by
            let _atomic_wd_1_0 := _object_w5
            exact Litex.Lt _atomic_wd_1_0 _value_i2) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    exact (Litex.modStrictUpper _atomic_wd_1_0 h_31 h_32))
                )
            )
          have h_828 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (_object_w6).val.right _value_i2 (by
                    let _atomic_wd_1_1 := _object_w5
                    exact h_4) h_5)
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 (And.intro h_4 h_5))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_quotient_x5f_remainder_x5f_decomposition_x2f_statement_x2e_lit
