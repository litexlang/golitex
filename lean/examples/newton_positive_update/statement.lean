import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_newton_x5f_positive_x5f_update_x2f_statement_x2e_lit

universe u v1 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (Litex.RPos (M := M))), (by
  have h_9 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i1 h_8)
        )
    )
  have h_11 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_9) _litex_zero.symm)
        )
    )
  exact Litex.In (let _wd_1_0 := (let _wd_2_0 := _value_i1;
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_8) h_11);
  (Litex.add _wd_2_0 _wd_2_1 (Litex.positiveRealToComplex _wd_2_0 h_8) (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_8) h_11)
    exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_8) (_atomic_wd_1_0).wd.2.2))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := _value_i1;
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_8) h_11);
    (Litex.add _wd_2_0 _wd_2_1 (Litex.positiveRealToComplex _wd_2_0 h_8) (by
      let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_8) h_11)
      exact (Litex.divInC _wd_1_1 _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_8) (_atomic_wd_2_0).wd.2.2))))
    exact (Litex.addInC _value_i1 (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex _value_i1 h_8) (Litex.divInC _wd_1_1 _value_i1 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i1 h_8) ((_atomic_wd_1_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.RPos (M := M))
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_8
    have h_9 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i1 h_8)
          )
      )
    have h_10 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_9)
          )
      )
    have h_11 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_9) _litex_zero.symm)
          )
      )
    have h_208 : Litex.In _value_i1 (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_8
          )
      )
    have h_209 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i1 h_208)
          )
      )
    have h_210 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_209)
          )
      )
    have h_211 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_209) _litex_zero.symm)
          )
      )
    have h_3 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
      (by
        litex_checked_step =>
          exact (
            h_209
          )
      )
    have h_4 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            h_211
          )
      )
    let _object_w4 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _value_i1 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i1 h_208) h_211)

    have h_5 : (by
      let _atomic_wd_1_0 := _object_w4
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w4
              exact (by
                let _litex_positive_result := _atomic_wd_1_0
                exact Litex.divPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2.1 _litex_positive_result.wd.2.2 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_209
              ))
          )
      )
    let _object_w5 := (let _wd_1_0 := _value_i1;
    let _wd_1_1 := _object_w4;
    (Litex.add _wd_1_0 _wd_1_1 (Litex.positiveRealToComplex _wd_1_0 h_208) (by
      let _atomic_wd_1_0 := _object_w4
      exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_1_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_1_0 h_208) (_atomic_wd_1_0).wd.2.2))))

    have h_6 : (by
      let _atomic_wd_1_0 := _object_w5
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w5
              exact (by
                let _litex_positive_result := _atomic_wd_1_0
                exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 h_3 (by
                let _atomic_wd_2_0 := _object_w4
                exact h_5)
              ))
          )
      )
    let _object_w6 := (let _wd_1_0 := _object_w5;
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w5
      exact (Litex.addInC _value_i1 (_object_w5).val.right (Litex.positiveRealToComplex _value_i1 h_208) (Litex.divInC _wd_1_1 _value_i1 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i1 h_208) ((_object_w5).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

    have h_7 : (by
      let _atomic_wd_1_0 := _object_w6
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w6
              exact (by
                let _litex_positive_result := _atomic_wd_1_0
                exact Litex.divPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2.1 _litex_positive_result.wd.2.2 (by
                let _atomic_wd_2_1 := _object_w5
                exact h_6) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))
              ))
          )
      )
    exact (by
      let _atomic_wd_1_0 := _object_w6
      exact (Litex.inRPos_intro _atomic_wd_1_0 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_7; exact (M.real_members (Litex.denote _atomic_wd_1_0)).mpr ⟨_litex_real, _litex_value⟩) h_7))
  )

noncomputable def _object_i2 := (Litex.formulaFnTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i3 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i3)) (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.divValue (M.number (2 : ℂ)) _raw_i3)) (M.number (2 : ℂ)))) (by
  intro _raw_i3 h_1015 _positive_i3
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1015)
  have h_1015 : Litex.In _value_i3 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i3).mpr ⟨h_1015, _positive_i3⟩)
  have h_1016 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i3 h_1015)
        )
    )
  have h_1017 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_1016)
        )
    )
  have h_1018 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_1016) _litex_zero.symm)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _value_i3;
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1015) h_1018);
    (Litex.add _wd_2_0 _wd_2_1 (Litex.positiveRealToComplex _wd_2_0 h_1015) (by
      let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1015) h_1018)
      exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1015) (_atomic_wd_2_0).wd.2.2))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := (let _wd_2_0 := _value_i3;
      let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1015) h_1018);
      (Litex.add _wd_2_0 _wd_2_1 (Litex.positiveRealToComplex _wd_2_0 h_1015) (by
        let _atomic_wd_3_0 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1015) h_1018)
        exact (Litex.divInC _wd_1_1 _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1015) (_atomic_wd_3_0).wd.2.2))))
      exact (Litex.addInC _value_i3 (_atomic_wd_2_0).val.right (Litex.positiveRealToComplex _value_i3 h_1015) (Litex.divInC _wd_1_1 _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i3 h_1015) ((_atomic_wd_2_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
    exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _value_i3;
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1015) h_1018);
    (Litex.add _wd_2_0 _wd_2_1 (Litex.positiveRealToComplex _wd_2_0 h_1015) (by
      let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1015) h_1018)
      exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1015) (_atomic_wd_2_0).wd.2.2))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := (let _wd_2_0 := _value_i3;
      let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1015) h_1018);
      (Litex.add _wd_2_0 _wd_2_1 (Litex.positiveRealToComplex _wd_2_0 h_1015) (by
        let _atomic_wd_3_0 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1015) h_1018)
        exact (Litex.divInC _wd_1_1 _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1015) (_atomic_wd_3_0).wd.2.2))))
      exact (Litex.addInC _value_i3 (_atomic_wd_2_0).val.right (Litex.positiveRealToComplex _value_i3 h_1015) (Litex.divInC _wd_1_1 _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i3 h_1015) ((_atomic_wd_2_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
    exact (by
      have h_5605 : Litex.In _value_i3 (Litex.RPos (M := M)) :=
        h_1015
      exact (Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (congrArg₂ M.divValue (congrArg₂ M.addValue (Litex.sameRefl _value_i3) (congrArg₂ M.divValue (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (Litex.sameRefl _value_i3))) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))) (Litex.sameRefl (Litex.RPos (M := M))) ((h_2 (M := M)) _value_i3 h_5605))
    ))))
theorem h_5614 : Litex.In (_object_i2 (M := M)) (Litex.fnSet ((_object_i2 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i2 (M := M)))
theorem h_5615 : Litex.Same (_object_i2 (M := M)) (_object_i2 (M := M)) :=
  (Litex.sameRefl (_object_i2 (M := M)))

theorem h_5617 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_5631 : Litex.In _value_i4 (Litex.RPos (M := M))), (by
  let _object_w13 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i3 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i3)) (_object_i2 (M := M)) _value_i4 (h_5614 (M := M)) (Litex.inRPos_real _value_i4 h_5631) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i4)).mp h_5631).2)
  exact (by
    let _atomic_wd_1_0 := _object_w13
    exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M)))
) :=
  (by
    intro _Host_i4 _rep_i4 _value_i4 h_5631
    have h_5632 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i4 h_5631)
          )
      )
    have h_5633 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i4 h_5632)
          )
      )
    have h_5634 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i4 h_5632) _litex_zero.symm)
          )
      )
    let _object_w13 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i3 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i3)) (_object_i2 (M := M)) _value_i4 (h_5614 (M := M)) (Litex.inRPos_real _value_i4 h_5631) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i4)).mp h_5631).2)
    have h_5616 : (by
      let _atomic_wd_1_0 := _object_w13
      exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w13
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))
          )
      )
    have h_5666 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_w13 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _object_w13 h_5616)
          )
      )
    have h_5667 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w13 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _object_w13 h_5666)
          )
      )
    have h_5668 : ¬ Litex.Same _object_w13 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _object_w13 h_5666) _litex_zero.symm)
          )
      )
    exact h_5616
  )

noncomputable def _object_w14 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i3 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i3)) (_object_i2 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_5614 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (1 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))).2)

theorem h_5669 : (by
  let _atomic_wd_1_0 := (_object_w14 (M := M))
  exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M))) :=
  (by
    let _atomic_wd_1_0 := (_object_w14 (M := M))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))

theorem h_5689 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (_object_w14 (M := M)) :=
  (Litex.inRPos_positive (_object_w14 (M := M)) (h_5669 (M := M)))

theorem h_5690 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (_object_w14 (M := M)) :=
  (Litex.ltToLe (Litex.number (M := M) 0) (_object_w14 (M := M)) (h_5689 (M := M)))

theorem h_5691 : ¬ Litex.Same (_object_w14 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (_object_w14 (M := M)) (h_5689 (M := M))) _litex_zero.symm)

noncomputable def _object_w16 := (Litex.div (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_5692 : (by
  let _equal_wd_1_0 := (_object_w14 (M := M))
  let _equal_wd_1_1 := (_object_w16 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (1 : ℂ))) = (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) from by
    have _litex_residual : (M.divValue (M.addValue (M.number (1 : ℂ)) (M.divValue (M.number (2 : ℂ)) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) = (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) := (let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_0 (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_0 (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) / (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ))))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
      let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_0 (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
      (Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
        let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_0 (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) / (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ))))))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_1_0).val.right).wd.1 ((_atomic_wd_1_0).val.right).wd.2.1 ((_atomic_wd_1_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + ((2 : ℂ) / (1 : ℂ))) = (3 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
    let _equal_wd_2_1 := (Litex.div (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 (((1 : ℂ) + ((2 : ℂ) / (1 : ℂ))) / (2 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (_equal_wd_2_0).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_2_0).val.left).val.right ((_equal_wd_2_0).val.left).wd.1 ((_equal_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (((_equal_wd_2_0).val.left).val.right).wd.1 (((_equal_wd_2_0).val.left).val.right).wd.2.1 (((_equal_wd_2_0).val.left).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2.1 (_equal_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (1 : ℂ))))).trans (by
    let _litex_original := (_object_w14 (M := M))
    let _litex_literal := (let _wd_1_0 := (_object_i2 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i3 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i3)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))).2))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_5615 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i3 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i3)) (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.divValue (M.number (2 : ℂ)) _raw_i3)) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i3 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i3)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.divValue (M.number (2 : ℂ)) _raw_i3)) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (M.number (1 : ℂ)) (M.divValue (M.number (2 : ℂ)) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) from rfl))
  ))).trans _litex_residual)
end LitexCompiled.file_lean_x2f_examples_x2f_newton_x5f_positive_x5f_update_x2f_statement_x2e_lit
