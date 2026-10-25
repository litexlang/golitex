import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_newton_x5f_residual_x5f_bound_x2f_statement_x2e_lit

universe u v3 v6 v7 v9 v13 v17 v19 v22 v24 v26 v28 v29 v31 v33 v35 v38 v39
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_14 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (M.real_subset_complex _ h_14)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.numberInC (M := M) (2 : ℂ))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_14 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (M.real_subset_complex _ h_14)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.numberInC (M := M) (2 : ℂ))))
    exact (Litex.subInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (by
      let _litex_power := (_atomic_wd_1_0).val.left
      have _elaborated_power_base := h_14
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInR _litex_power _recorded_power_base
    ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))))))
theorem h_96 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_97 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_99 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_105 : Litex.In _value_i3 (Litex.RPos (M := M))), (by
  have h_106 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i3 h_105)
        )
    )
  have h_108 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_106) _litex_zero.symm)
        )
    )
  exact Litex.In (let _wd_1_0 := (let _wd_2_0 := _value_i3;
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_105) h_108);
  (Litex.add _wd_2_0 _wd_2_1 (Litex.positiveRealToComplex _wd_2_0 h_105) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_105) (_atomic_wd_1_0).wd.2.2))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC _value_i3 (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex _value_i3 h_105) (Litex.divInC _wd_1_1 _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i3 h_105) ((_atomic_wd_1_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.RPos (M := M))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_105
          have h_106 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i3 h_105)
                )
            )
          have h_107 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_106)
                )
            )
          have h_108 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_106) _litex_zero.symm)
                )
            )
          have h_365 : Litex.In _value_i3 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_105
                )
            )
          have h_366 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i3 h_365)
                )
            )
          have h_367 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_366)
                )
            )
          have h_368 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_366) _litex_zero.symm)
                )
            )
          have h_100 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  h_366
                )
            )
          have h_101 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_368
                )
            )
          let _object_w9 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i3 h_365) h_368)

          have h_102 : (by
            let _atomic_wd_1_0 := _object_w9
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    exact (by
                      let _litex_positive_result := _atomic_wd_1_0
                      exact Litex.divPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2.1 _litex_positive_result.wd.2.2 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_366
                    ))
                )
            )
          let _object_w10 := (let _wd_1_0 := _value_i3;
          let _wd_1_1 := _object_w9;
          (Litex.add _wd_1_0 _wd_1_1 (Litex.positiveRealToComplex _wd_1_0 h_365) (by
            let _atomic_wd_1_0 := _object_w9
            exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_1_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_1_0 h_365) (_atomic_wd_1_0).wd.2.2))))

          have h_103 : (by
            let _atomic_wd_1_0 := _object_w10
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w10
                    exact (by
                      let _litex_positive_result := _atomic_wd_1_0
                      exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 h_100 (by
                      let _atomic_wd_2_0 := _object_w9
                      exact h_102)
                    ))
                )
            )
          let _object_w11 := (let _wd_1_0 := _object_w10;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w10
            exact (Litex.addInC _value_i3 (_object_w10).val.right (Litex.positiveRealToComplex _value_i3 h_365) (Litex.divInC _wd_1_1 _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i3 h_365) ((_object_w10).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

          have h_104 : (by
            let _atomic_wd_1_0 := _object_w11
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w11
                    exact (by
                      let _litex_positive_result := _atomic_wd_1_0
                      exact Litex.divPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2.1 _litex_positive_result.wd.2.2 (by
                      let _atomic_wd_2_1 := _object_w10
                      exact h_103) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
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
            let _atomic_wd_1_0 := _object_w11
            exact (Litex.inRPos_intro _atomic_wd_1_0 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_104; exact (M.real_members (Litex.denote _atomic_wd_1_0)).mpr ⟨_litex_real, _litex_value⟩) h_104))
        )
      )
  )

noncomputable def _object_i4 := (Litex.formulaFnTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (by
  intro _raw_i5 h_1417 _positive_i5
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1417)
  have h_1417 : Litex.In _value_i5 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i5).mpr ⟨h_1417, _positive_i5⟩)
  have h_1418 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i5 h_1417)
        )
    )
  have h_1419 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i5 h_1418)
        )
    )
  have h_1420 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i5 h_1418) _litex_zero.symm)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _value_i5;
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1417) h_1420);
    (Litex.add _wd_2_0 _wd_2_1 (Litex.positiveRealToComplex _wd_2_0 h_1417) (by
      let _atomic_wd_2_0 := _wd_2_1
      exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1417) (_atomic_wd_2_0).wd.2.2))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (Litex.addInC _value_i5 (_atomic_wd_2_0).val.right (Litex.positiveRealToComplex _value_i5 h_1417) (Litex.divInC _wd_1_1 _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i5 h_1417) ((_atomic_wd_2_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
    exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _value_i5;
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1417) h_1420);
    (Litex.add _wd_2_0 _wd_2_1 (Litex.positiveRealToComplex _wd_2_0 h_1417) (by
      let _atomic_wd_2_0 := _wd_2_1
      exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_1417) (_atomic_wd_2_0).wd.2.2))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (Litex.addInC _value_i5 (_atomic_wd_2_0).val.right (Litex.positiveRealToComplex _value_i5 h_1417) (Litex.divInC _wd_1_1 _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i5 h_1417) ((_atomic_wd_2_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
    exact (by
      have h_7450 : Litex.In _value_i5 (Litex.RPos (M := M)) :=
        h_1417
      exact (Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (congrArg₂ M.divValue (congrArg₂ M.addValue (Litex.sameRefl _value_i5) (congrArg₂ M.divValue (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (Litex.sameRefl _value_i5))) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))) (Litex.sameRefl (Litex.RPos (M := M))) ((h_99 (M := M)) _value_i5 h_7450))
    ))))
theorem h_7459 : Litex.In (_object_i4 (M := M)) (Litex.fnSet ((_object_i4 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M)))
      )
  )
theorem h_7460 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M)))
      )
  )

theorem h_7464 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_7466 : Litex.In _value_i6 (Litex.N (M := M))), ((Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_7466
          have h_7467 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i6 h_7466)
                )
            )
          have h_7495 : Litex.In _value_i6 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_7466
                )
            )
          have h_7496 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i6 h_7495)
                )
            )
          have h_7465 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  h_7496
                )
            )
          exact (Litex.integerSuccessorTail _value_i6 (Litex.number (M := M) (0 : ℂ)) (Litex.naturalToInteger _value_i6 h_7495) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) h_7465)
        )
      )
  )

theorem h_7614 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_7617 : Litex.In _value_i7 (Litex.N (M := M))) (h_7612 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7), Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i7 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i7 h_7617) (Litex.numberInC (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_7617 h_7612
          have h_7618 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i7 h_7617)
                )
            )
          have h_7738 : Litex.In _value_i7 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_7617
                )
            )
          have h_7739 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i7 h_7738)
                )
            )
          let _object_w30 := (Litex.sub _value_i7 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i7 h_7738) (Litex.numberInC (M := M) (1 : ℂ)))

          have h_7615 : (by
            let _atomic_wd_1_0 := _object_w30
            exact Litex.In _atomic_wd_1_0 (Litex.N (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w30
                    exact (Litex.predecessorInN _atomic_wd_1_0 h_7738 h_7612 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
                )
            )

          have h_7825 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w30 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _object_w30 h_7615)
                )
            )
          have h_7616 : (by
            let _atomic_wd_1_0 := _object_w30
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w30
                    exact h_7825)
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w30
            exact h_7616)
        )
      )
  )

noncomputable def _object_i8 := (Litex.recursiveNatFnTarget (M := M) (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_index : ℕ) (_argument : M.Value) => (((∃ (_r _s : ℝ), _argument = M.number (_r : ℂ) ∧ (M.number (_index : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _argument = M.number (_s : ℂ) ∧ _r ≤ _s)))) (M.number (1 : ℂ)) (fun (_index : ℕ) (_prefix : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FunctionSemantics.callValue (M := M) _prefix (M.subValue (M.number (_index : ℂ)) (M.number (1 : ℂ)))))) (by
  intro _index _argument _member _guard
  exact Litex.NativeBridge.naturalValue_lt_number _index _argument _member _guard.1) (by
  let _raw_i9 : M.Value := (M.number 0)
  have h_7994 : M.mem _raw_i9 (M.standard .natural) := (show M.mem (M.number 0) (M.standard .natural) from (M.natural_members _).mpr ⟨0, by simp only [Nat.cast_zero]⟩)
  let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_7994)
  have h_7994 : Litex.In _value_i9 (Litex.N (M := M)) := h_7994
  have h_7995 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.naturalNonnegative _value_i9 h_7994)
        )
    )
  have h_7996 : Litex.In _value_i9 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.naturalToInteger _value_i9 h_7994)
        )
    )
  have h_8012 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num))
        )
    )
  have h_8019 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
    (by
      litex_checked_step =>
        exact (
          h_7995
        )
    )
  have h_8053 : ((Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            have h_8642 : Litex.In _value_i9 (Litex.N (M := M)) :=
              h_7994
            exact ((fun _known_tail => Or.elim _known_tail (fun _known_or_0 => Or.inl (Eq.trans (Eq.symm (Litex.sameRefl _value_i9)) (Eq.trans _known_or_0 (Litex.sameRefl (Litex.number (M := M) (0 : ℂ)))))) (fun _known_rest => Or.inr ((fun _known_or_1 => (Litex.ltOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _value_i9 _value_i9 (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (Litex.sameRefl _value_i9) _known_or_1)) _known_rest))) ((h_7464 (M := M)) _value_i9 h_8642))
          )
        )
    )
  have _disjoint_0_1 : Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) → ¬ Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 := by
    intro h_7990
    exact (by
      let _left := _value_i9
      let _right := (Litex.number (M := M) (0 : ℂ))
      have _leftReal : Litex.In _left Litex.R := (Litex.naturalToReal _value_i9 h_7994)
      have _rightReal : Litex.In _right Litex.R := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
      exact fun _opposite => not_lt_of_ge ((Litex.NativeBridge.le_iff_asReal _left _right _leftReal _rightReal).mp (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) _value_i9 _value_i9 (Litex.number (M := M) (0 : ℂ)) (h_7990).symm h_7990 h_7995)) ((Litex.NativeBridge.lt_iff_asReal _right _left _rightReal _leftReal).mp _opposite))
  have h_7990 : Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) := rfl
  have _checked_body := (Litex.number (M := M) (1 : ℂ))
  exact (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))) (by
  intro _index _prefix _prefix_member
  let _raw_i9 : M.Value := (M.number ((_index + 1 : ℕ) : ℂ))
  have h_7994 : M.mem _raw_i9 (M.standard .natural) := (Litex.NativeBridge.numberInN (M := M) (_index + 1))
  let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_7994)
  have h_7994 : Litex.In _value_i9 (Litex.N (M := M)) := h_7994
  have h_7995 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.naturalNonnegative _value_i9 h_7994)
        )
    )
  have h_7996 : Litex.In _value_i9 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.naturalToInteger _value_i9 h_7994)
        )
    )
  have h_8012 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num))
        )
    )
  have h_8019 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
    (by
      litex_checked_step =>
        exact (
          h_7995
        )
    )
  have h_8053 : ((Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            have h_8642 : Litex.In _value_i9 (Litex.N (M := M)) :=
              h_7994
            exact ((fun _known_tail => Or.elim _known_tail (fun _known_or_0 => Or.inl (Eq.trans (Eq.symm (Litex.sameRefl _value_i9)) (Eq.trans _known_or_0 (Litex.sameRefl (Litex.number (M := M) (0 : ℂ)))))) (fun _known_rest => Or.inr ((fun _known_or_1 => (Litex.ltOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _value_i9 _value_i9 (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (Litex.sameRefl _value_i9) _known_or_1)) _known_rest))) ((h_7464 (M := M)) _value_i9 h_8642))
          )
        )
    )
  have _disjoint_0_1 : Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) → ¬ Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 := by
    intro h_7990
    exact (by
      let _left := _value_i9
      let _right := (Litex.number (M := M) (0 : ℂ))
      have _leftReal : Litex.In _left Litex.R := (Litex.naturalToReal _value_i9 h_7994)
      have _rightReal : Litex.In _right Litex.R := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
      exact fun _opposite => not_lt_of_ge ((Litex.NativeBridge.le_iff_asReal _left _right _leftReal _rightReal).mp (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) _value_i9 _value_i9 (Litex.number (M := M) (0 : ℂ)) (h_7990).symm h_7990 h_7995)) ((Litex.NativeBridge.lt_iff_asReal _right _left _rightReal _leftReal).mp _opposite))
  let _object_i8 := Litex.semanticObject (M := M) _prefix (M.member_isSet _prefix_member)
  have h_8052 : Litex.In _object_i8 (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i10 : M.Value) => (((∃ (_r _s : ℝ), _raw_i10 = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i10 = M.number (_s : ℂ) ∧ _r ≤ _s)))))) := _prefix_member
  have h_7991 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 := (by
    refine ⟨0, ((_index + 1 : ℕ) : ℝ), rfl, ?_, ?_⟩
    · change M.number ((_index + 1 : ℕ) : ℂ) = M.number (((_index + 1 : ℕ) : ℝ) : ℂ)
      simp only [Complex.ofReal_natCast]
    · exact_mod_cast Nat.zero_lt_succ _index)
  have _checked_body := (let _object_w39 := (let _object_w38 := (Litex.sub _value_i9 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i9 h_7994) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i10 : M.Value) => (((∃ (_r _s : ℝ), _raw_i10 = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i10 = M.number (_s : ℂ) ∧ _r ≤ _s)))) _object_i8 _object_w38 h_8052 (by
    let _atomic_wd_1_0 := _object_w38
    exact (Litex.predecessorInN _atomic_wd_1_0 h_7994 h_7991 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))) (And.intro (by
    let _atomic_wd_1_0 := _object_w38
    exact (Litex.subtractOneLess _atomic_wd_1_0 (Litex.naturalToReal _value_i9 h_7994) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))) (by
    let _atomic_wd_1_0 := _object_w38
    exact (Litex.subNonnegative _atomic_wd_1_0 (Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _value_i9 _value_i9 ((Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))).symm (Litex.sameRefl _value_i9) (Litex.integerSuccessorLowerBound _value_i9 (Litex.naturalToInteger _value_i9 h_7994) h_7991)))))));
  (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _object_w39 (h_7459 (M := M)) (Litex.inRPos_real _object_w39 (by
    let _atomic_wd_1_0 := _object_w39
    exact (by
      let _litex_return_call := _object_w39
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w39)).mp (by
    let _atomic_wd_1_0 := _object_w39
    exact (by
      let _litex_return_call := _object_w39
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))).2))
  exact (by
    let _atomic_wd_1_0 := (let _object_w41 := (let _object_w40 := (Litex.sub _value_i9 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i9 h_7994) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i10 : M.Value) => (((∃ (_r _s : ℝ), _raw_i10 = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i10 = M.number (_s : ℂ) ∧ _r ≤ _s)))) _object_i8 _object_w40 h_8052 (by
      let _atomic_wd_2_0 := _object_w40
      exact (Litex.predecessorInN _atomic_wd_2_0 h_7994 h_7991 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))) (And.intro (by
      let _atomic_wd_2_0 := _object_w40
      exact (Litex.subtractOneLess _atomic_wd_2_0 (Litex.naturalToReal _value_i9 h_7994) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))) (by
      let _atomic_wd_2_0 := _object_w40
      exact (Litex.subNonnegative _atomic_wd_2_0 (Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _value_i9 _value_i9 ((Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))).symm (Litex.sameRefl _value_i9) (Litex.integerSuccessorLowerBound _value_i9 (Litex.naturalToInteger _value_i9 h_7994) h_7991)))))));
    (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _object_w41 (h_7459 (M := M)) (Litex.inRPos_real _object_w41 (by
      let _atomic_wd_2_0 := _object_w41
      exact (by
        let _litex_return_call := _object_w41
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w41)).mp (by
      let _atomic_wd_2_0 := _object_w41
      exact (by
        let _litex_return_call := _object_w41
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))).2))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) (by
  intro _index _left_prefix _right_prefix _agree
  let _raw_i9 : M.Value := (M.number ((_index + 1 : ℕ) : ℂ))
  have h_7994 : M.mem _raw_i9 (M.standard .natural) := (Litex.NativeBridge.numberInN (M := M) (_index + 1))
  let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_7994)
  have h_7994 : Litex.In _value_i9 (Litex.N (M := M)) := h_7994
  have h_7995 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.naturalNonnegative _value_i9 h_7994)
        )
    )
  have h_7991 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 := (by
    refine ⟨0, ((_index + 1 : ℕ) : ℝ), rfl, ?_, ?_⟩
    · change M.number ((_index + 1 : ℕ) : ℂ) = M.number (((_index + 1 : ℕ) : ℝ) : ℂ)
      simp only [Complex.ofReal_natCast]
    · exact_mod_cast Nat.zero_lt_succ _index)
  exact (congrArg (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M)))) (_agree (M.subValue (M.number ((_index + 1 : ℕ) : ℂ)) (M.number (1 : ℂ))) (by
    let _atomic_wd_1_0 := (Litex.sub _value_i9 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i9 h_7994) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.predecessorInN _atomic_wd_1_0 h_7994 h_7991 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))) (And.intro (by
    let _atomic_wd_1_0 := (Litex.sub _value_i9 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i9 h_7994) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.subtractOneLess _atomic_wd_1_0 (Litex.naturalToReal _value_i9 h_7994) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))) (by
    let _atomic_wd_1_0 := (Litex.sub _value_i9 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i9 h_7994) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.subNonnegative _atomic_wd_1_0 (Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _value_i9 _value_i9 ((Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))).symm (Litex.sameRefl _value_i9) (Litex.integerSuccessorLowerBound _value_i9 (Litex.naturalToInteger _value_i9 h_7994) h_7991)))))))))
theorem h_10028 : Litex.In (_object_i8 (M := M)) (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.natural) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
    intro _raw_i9 h_7992 _
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_7992)
    have h_7992 : Litex.In _value_i9 (Litex.N (M := M)) := h_7992
    have h_7993 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i9 h_7992)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True))) :=
  (Litex.recursiveNatFnInFnSet (_object_i8 (M := M)))
theorem h_10030 : ∀ {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_7994 : Litex.In _value_i9 Litex.N) (h_7990 : ((Litex.denote _value_i9) = (M.number (0 : ℂ)))), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i9)) = (M.number (1 : ℂ))) := by
  intro _Host_i9 _rep_i9 _value_i9 h_7994 h_7990
  rw [h_7990]
  exact Litex.recursiveNatFn_zero (_object_i8 (M := M))
theorem h_10032 : ∀ {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_7994 : Litex.In _value_i9 Litex.N) (h_7991 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r < _s)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i9)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.subValue (Litex.denote _value_i9) (M.number (1 : ℂ)))))) := by
  intro _Host_i9 _rep_i9 _value_i9 h_7994 h_7991
  let _index := Litex.NativeBridge.asNat _value_i9 h_7994
  have _index_spec : Litex.denote _value_i9 = M.number (_index : ℂ) := Litex.NativeBridge.asNat_spec _value_i9 h_7994
  have _index_positive : 0 < _index := Litex.NativeBridge.naturalValue_pos (Litex.denote _value_i9) h_7994 h_7991
  obtain ⟨_previous, _index_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt _index_positive)
  rw [_index_spec, _index_eq]
  exact Litex.recursiveNatFn_succ (_object_i8 (M := M)) _previous

noncomputable def _object_i11 := (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (by
  intro _raw_i12 h_10046 _
  let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_10046)
  have h_10046 : Litex.In _value_i12 (Litex.N (M := M)) := h_10046
  have h_10047 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.naturalNonnegative _value_i12 h_10046)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _object_w47 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i12 (h_10028 (M := M)) h_10046 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w47 (h_96 (M := M)) (by
      let _atomic_wd_2_0 := _object_w47
      exact (Litex.inRPos_real _object_w47 (Litex.callInOutput _object_w47))) True.intro));
    (Litex.abs _wd_1_0 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_return_call := _atomic_wd_2_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _object_w47 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i12 (h_10028 (M := M)) h_10046 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w47 (h_96 (M := M)) (by
      let _atomic_wd_2_0 := _object_w47
      exact (Litex.inRPos_real _object_w47 (Litex.callInOutput _object_w47))) True.intro));
    (Litex.abs _wd_1_0 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_return_call := _atomic_wd_2_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
    exact (by
      let _litex_abs := _atomic_wd_1_0
      exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
    ))))
theorem h_10610 : Litex.In (_object_i11 (M := M)) (Litex.fnSet ((_object_i11 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i11 (M := M)))
      )
  )
theorem h_10611 : Litex.Same (_object_i11 (M := M)) (_object_i11 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i11 (M := M)))
      )
  )

theorem h_10613 : ∀ {_Host_i13 : Type v13} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_10618 : Litex.In _value_i13 (Litex.N (M := M))), (by
  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
  let _wd_1_1 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_0 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) _value_i13 (Litex.NativeBridge.asNat _value_i13 h_10618) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_10618 (Litex.NativeBridge.asNat_spec _value_i13 h_10618));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (Litex.NativeBridge.asNat _wd_2_1 (by
    let _atomic_wd_2_0 := _wd_2_1
    exact (by
      let _litex_power := _atomic_wd_2_0
      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
      have _elaborated_power_exponent := h_10618
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
    ))) (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
    let _atomic_wd_2_0 := _wd_2_1
    exact (by
      let _litex_power := _atomic_wd_2_0
      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
      have _elaborated_power_exponent := h_10618
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
    )) (Litex.NativeBridge.asNat_spec _wd_2_1 (by
    let _atomic_wd_2_0 := _wd_2_1
    exact (by
      let _litex_power := _atomic_wd_2_0
      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
      have _elaborated_power_exponent := h_10618
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
    )))));
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
    let _atomic_wd_2_0 := _wd_1_1
    exact (by
      let _litex_power := _atomic_wd_2_0
      have _elaborated_power_base := (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_2_0).val.base ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_0 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (4 : ℂ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ))))
      have _elaborated_power_exponent := (by
      let _litex_power := (_atomic_wd_2_0).val.exponent
      have _elaborated_power_base := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _elaborated_power_exponent := h_10618
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.Z (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInZ _litex_power _recorded_power_base _recorded_power_exponent
    )
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))))
  exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i13 _rep_i13 _value_i13 h_10618
          have h_10619 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i13 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i13 h_10618)
                )
            )
          have h_10924 : Litex.In _value_i13 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10618
                )
            )
          have h_10925 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i13 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i13 h_10924)
                )
            )
          let _object_w57 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) _value_i13 (Litex.NativeBridge.asNat _value_i13 h_10924) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_10924 (Litex.NativeBridge.asNat_spec _value_i13 h_10924))

          have h_10614 : (by
            let _atomic_wd_1_0 := _object_w57
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w57
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                      have _elaborated_power_exponent := (Litex.naturalToInteger _value_i13 h_10924)
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInR _litex_power _recorded_power_base
                    ))
                )
            )
          let _object_w59 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

          have h_10615 : (by
            let _atomic_wd_1_0 := _object_w59
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w59
                    exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (4 : ℝ)) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num))))
                )
            )
          let _object_w60 := (let _wd_1_0 := _object_w59;
          let _wd_1_1 := _object_w57;
          (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w57
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := h_10924
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            ))) (by
            let _atomic_wd_1_0 := _object_w59
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
            let _atomic_wd_1_0 := _object_w57
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := h_10924
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w57
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := h_10924
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            )))))

          have h_10616 : (by
            let _atomic_wd_1_0 := _object_w60
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w60
                    exact (by
                      let _atomic_wd_2_1 := _atomic_wd_1_0
                      exact (Litex.powStructuralPositiveOfPositive _atomic_wd_2_1 (by
                        let _atomic_wd_3_1 := _object_w59
                        exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_3_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                          let _atomic_wd_4_0 := _object_w59
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).mpr (by
                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_3_1 (by
                          let _atomic_wd_4_0 := _object_w59
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (4 : ℝ)) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_3_1 (by
                          let _atomic_wd_4_0 := _object_w59
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))))
                )
            )
          let _object_w61 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_1_1 := _object_w60;
          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _object_w60
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.NativeBridge.inOfDenoteNumber (_object_w60).val.base ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (4 : ℂ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ))))
              have _elaborated_power_exponent := (by
              let _litex_power := (_object_w60).val.exponent
              have _elaborated_power_base := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _elaborated_power_exponent := h_10924
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.Z (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInZ _litex_power _recorded_power_base _recorded_power_exponent
            )
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))))

          have h_10617 : (by
            let _atomic_wd_1_0 := _object_w61
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w61
                    exact (by
                      let _litex_positive_result := _atomic_wd_1_0
                      exact Litex.mulPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (by
                      let _atomic_wd_2_1 := _object_w60
                      exact h_10616)
                    ))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w61
            exact (Litex.inRPos_intro _atomic_wd_1_0 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_10617; exact (M.real_members (Litex.denote _atomic_wd_1_0)).mpr ⟨_litex_real, _litex_value⟩) h_10617))
        )
      )
  )

noncomputable def _object_i15 := (Litex.formulaFnTarget (M := M) Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (by
  intro _raw_i16 h_12413 _
  let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_12413)
  have h_12413 : Litex.In _value_i16 (Litex.N (M := M)) := h_12413
  have h_12414 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.naturalNonnegative _value_i16 h_12413)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_1_1 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_0 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    let _wd_2_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) _value_i16 (Litex.NativeBridge.asNat _value_i16 h_12413) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_12413 (Litex.NativeBridge.asNat_spec _value_i16 h_12413));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (Litex.NativeBridge.asNat _wd_2_1 (by
      let _atomic_wd_2_0 := _wd_2_1
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_12413
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      ))) (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
      let _atomic_wd_2_0 := _wd_2_1
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_12413
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.NativeBridge.asNat_spec _wd_2_1 (by
      let _atomic_wd_2_0 := _wd_2_1
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_12413
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      )))));
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_2_0).val.base ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_0 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (4 : ℂ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ))))
        have _elaborated_power_exponent := (by
        let _litex_power := (_atomic_wd_2_0).val.exponent
        have _elaborated_power_base := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _elaborated_power_exponent := h_12413
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.Z (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInZ _litex_power _recorded_power_base _recorded_power_exponent
      )
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))))
    exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_1_1 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_0 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    let _wd_2_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) _value_i16 (Litex.NativeBridge.asNat _value_i16 h_12413) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_12413 (Litex.NativeBridge.asNat_spec _value_i16 h_12413));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (Litex.NativeBridge.asNat _wd_2_1 (by
      let _atomic_wd_2_0 := _wd_2_1
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_12413
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      ))) (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
      let _atomic_wd_2_0 := _wd_2_1
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_12413
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.NativeBridge.asNat_spec _wd_2_1 (by
      let _atomic_wd_2_0 := _wd_2_1
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_12413
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      )))));
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_2_0).val.base ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_0 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (4 : ℂ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ))))
        have _elaborated_power_exponent := (by
        let _litex_power := (_atomic_wd_2_0).val.exponent
        have _elaborated_power_base := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _elaborated_power_exponent := h_12413
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.Z (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInZ _litex_power _recorded_power_base _recorded_power_exponent
      )
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))))
    exact (by
      have h_20125 : Litex.In _value_i16 (Litex.N (M := M)) :=
        h_12413
      exact (Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (congrArg₂ M.mulValue (Litex.sameRefl (Litex.number (M := M) (4 : ℂ))) (congrArg₂ M.powValue (Litex.sameRefl ((_atomic_wd_1_0).val.right).val.base) (congrArg₂ M.powValue (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (Litex.sameRefl _value_i16)))) (Litex.sameRefl (Litex.RPos (M := M))) ((h_10613 (M := M)) _value_i16 h_20125))
    ))))
theorem h_20132 : Litex.In (_object_i15 (M := M)) (Litex.fnSet ((_object_i15 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i15 (M := M)))
      )
  )
theorem h_20133 : Litex.Same (_object_i15 (M := M)) (_object_i15 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i15 (M := M)))
      )
  )

noncomputable def _object_w70 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_7459 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (1 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))).2)

noncomputable def _object_w71 := (Litex.div (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_20134 : (by
  let _equal_wd_1_0 := (_object_w70 (M := M))
  let _equal_wd_1_1 := (_object_w71 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w70 (M := M));
        let _equal_wd_1_1 := (_object_w71 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (1 : ℂ))) = (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) from by
          have _litex_residual : (M.divValue (M.addValue (M.number (1 : ℂ)) (M.divValue (M.number (2 : ℂ)) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) = (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) := (let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_0 (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) / (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ))))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_1_0).val.right).wd.1 ((_atomic_wd_1_0).val.right).wd.2.1 ((_atomic_wd_1_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + ((2 : ℂ) / (1 : ℂ))) = (3 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
          let _equal_wd_2_1 := _equal_wd_1_1;
          (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 (((1 : ℂ) + ((2 : ℂ) / (1 : ℂ))) / (2 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (_equal_wd_2_0).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_2_0).val.left).val.right ((_equal_wd_2_0).val.left).wd.1 ((_equal_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (((_equal_wd_2_0).val.left).val.right).wd.1 (((_equal_wd_2_0).val.left).val.right).wd.2.1 (((_equal_wd_2_0).val.left).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2.1 (_equal_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (1 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (1 : ℂ))) = (M.divValue (M.addValue (M.number (1 : ℂ)) (M.divValue (M.number (2 : ℂ)) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))).2))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_7460 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (M.number (1 : ℂ)) (M.divValue (M.number (2 : ℂ)) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

theorem h_20709 : (by
  let _chain_wd_20709_0 := (let _wd_1_0 := (_object_w71 (M := M));
  (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _wd_1_0 (h_7459 (M := M)) (Litex.inRPos_real _wd_1_0 (by
    let _atomic_wd_1_0 := (_object_w71 (M := M))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_0)).mp (by
    let _atomic_wd_1_0 := (_object_w71 (M := M))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))).2))
  let _chain_wd_20709_1 := (let _wd_1_0 := (let _wd_2_0 := (_object_w71 (M := M));
  let _wd_2_1 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_3_1 := (_object_w71 (M := M));
  (Litex.div _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
    let _atomic_wd_1_0 := (_object_w71 (M := M))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
    let _atomic_wd_1_0 := (_object_w71 (M := M))
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := (_object_w71 (M := M))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
  let _chain_wd_20709_2 := _chain_wd_20709_1
  let _chain_wd_20709_3 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact ((by
    let _equal_wd_1_0 := _chain_wd_20709_0
    let _equal_wd_1_1 := _chain_wd_20709_1
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _chain_wd_20709_2
    let _equal_wd_1_1 := _chain_wd_20709_3
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _chain_wd_20709_0 := (let _wd_1_0 := (_object_w71 (M := M));
          (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _wd_1_0 (h_7459 (M := M)) (Litex.inRPos_real _wd_1_0 (by
            let _atomic_wd_1_0 := (_object_w71 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_0)).mp (by
            let _atomic_wd_1_0 := (_object_w71 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))).2))
          let _chain_wd_20709_1 := (let _wd_1_0 := (let _wd_2_0 := (_object_w71 (M := M));
          let _wd_2_1 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_3_1 := (_object_w71 (M := M));
          (Litex.div _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
            let _atomic_wd_1_0 := (_object_w71 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
            let _atomic_wd_1_0 := (_object_w71 (M := M))
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := (_object_w71 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
          let _chain_wd_20709_2 := _chain_wd_20709_1
          let _chain_wd_20709_3 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
          exact (And.intro (let _equal_wd_1_0 := _chain_wd_20709_0;
          let _equal_wd_1_1 := _chain_wd_20709_1;
          (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ)))) = (M.divValue (M.addValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.divValue (M.number (2 : ℂ)) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))))) (M.number (2 : ℂ))) from by
            have _litex_residual : (M.divValue (M.addValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.divValue (M.number (2 : ℂ)) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))))) (M.number (2 : ℂ))) = (M.divValue (M.addValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.divValue (M.number (2 : ℂ)) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))))) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ)))) = (M.divValue (M.addValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.divValue (M.number (2 : ℂ)) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))))) (M.number (2 : ℂ))) from by
            let _litex_original := _equal_wd_1_0
            let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
            let _wd_1_1 := (_object_w71 (M := M));
            (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 (by
              let _atomic_wd_1_0 := (_object_w71 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp (by
              let _atomic_wd_1_0 := (_object_w71 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))).2))
            have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_7460 (M := M)) (Litex.sameRefl _litex_original.val.argument)
            have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.divValue (M.number (2 : ℂ)) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))))) (M.number (2 : ℂ))) from rfl))
          ))).trans _litex_residual))) (let _equal_wd_1_0 := _chain_wd_20709_2;
          let _equal_wd_1_1 := _chain_wd_20709_3;
          (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((((3 : ℂ) / (2 : ℂ)) + ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ)))) / (2 : ℂ)) ((17 : ℂ) / (12 : ℂ)) (Litex.NativeBridge.denoteDiv (_equal_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd ((_equal_wd_1_0).val.left).val.left ((_equal_wd_1_0).val.left).val.right ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (((_equal_wd_1_0).val.left).val.right).val.right (((_equal_wd_1_0).val.left).val.right).wd.1 (((_equal_wd_1_0).val.left).val.right).wd.2.1 (((_equal_wd_1_0).val.left).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (by norm_num))))))
      )
  )

theorem h_21877 : Litex.Same (let _wd_1_0 := (_object_w71 (M := M));
(Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _wd_1_0 (h_7459 (M := M)) (Litex.inRPos_real _wd_1_0 (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_0)).mp (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))).2)) (let _wd_1_0 := (let _wd_2_0 := (_object_w71 (M := M));
let _wd_2_1 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
let _wd_3_1 := (_object_w71 (M := M));
(Litex.div _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
(Litex.add _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := _wd_2_1
  exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) :=
  (by
    litex_complete =>
      exact (
        (And.left (h_20709 (M := M)))
      )
  )

theorem h_21878 : Litex.Same (let _wd_1_0 := (let _wd_2_0 := (_object_w71 (M := M));
let _wd_2_1 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
let _wd_3_1 := (_object_w71 (M := M));
(Litex.div _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
(Litex.add _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := _wd_2_1
  exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) :=
  (by
    litex_complete =>
      exact (
        (And.right (h_20709 (M := M)))
      )
  )

theorem h_21879 : Litex.Same (let _wd_1_0 := (_object_w71 (M := M));
(Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _wd_1_0 (h_7459 (M := M)) (Litex.inRPos_real _wd_1_0 (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_0)).mp (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))).2)) (let _wd_1_0 := (let _wd_2_0 := (_object_w71 (M := M));
let _wd_2_1 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
let _wd_3_1 := (_object_w71 (M := M));
(Litex.div _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
(Litex.add _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := _wd_2_1
  exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) :=
  (by
    litex_complete =>
      exact (
        (h_21877 (M := M))
      )
  )

theorem h_21880 : Litex.Same (let _wd_1_0 := (let _wd_2_0 := (_object_w71 (M := M));
let _wd_2_1 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
let _wd_3_1 := (_object_w71 (M := M));
(Litex.div _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
(Litex.add _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := _wd_2_1
  exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) :=
  (by
    litex_complete =>
      exact (
        (h_21878 (M := M))
      )
  )

theorem h_21881 : Litex.Same (let _wd_1_0 := (_object_w71 (M := M));
(Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _wd_1_0 (h_7459 (M := M)) (Litex.inRPos_real _wd_1_0 (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_0)).mp (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))).2)) (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) :=
  (by
    litex_complete =>
      exact (
        (Eq.trans (h_21877 (M := M)) (h_21878 (M := M)))
      )
  )

noncomputable def _object_w74 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_96 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)

noncomputable def _object_w75 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))

theorem h_21882 : (by
  let _equal_wd_1_0 := (_object_w74 (M := M))
  let _equal_wd_1_1 := (_object_w75 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w74 (M := M));
        let _equal_wd_1_1 := (_object_w75 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ))) = (M.negValue (M.number (1 : ℂ))) from by
          have _litex_residual : (M.subValue (M.powValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) = (M.negValue (M.number (1 : ℂ))) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) ^ (2 : ℕ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ))));
          let _equal_wd_2_1 := _equal_wd_1_1;
          (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 (((1 : ℂ) ^ (2 : ℕ)) - (2 : ℂ)) (- (1 : ℂ)) (Litex.NativeBridge.denoteSub (_equal_wd_2_0).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ))) = (M.subValue (M.powValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_97 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (M.powValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w76 := (let _wd_1_0 := (_object_w71 (M := M));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
  let _atomic_wd_1_0 := (_object_w71 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro))

noncomputable def _object_w77 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_22340 : (by
  let _equal_wd_1_0 := (_object_w76 (M := M))
  let _equal_wd_1_1 := (_object_w77 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w76 (M := M));
        let _equal_wd_1_1 := (_object_w77 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ)))) = (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) from by
          have _litex_residual : (M.subValue (M.powValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) := (let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := (_object_w71 (M := M));
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := (_object_w71 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((9 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_2_0 := (_object_w71 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))).trans (congrArg M.number (by norm_num : (((3 : ℂ) / (2 : ℂ)) ^ (2 : ℕ)) = ((9 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((9 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ))));
          let _equal_wd_2_1 := _equal_wd_1_1;
          (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 ((((3 : ℂ) / (2 : ℂ)) ^ (2 : ℕ)) - (2 : ℂ)) ((1 : ℂ) / (4 : ℂ)) (Litex.NativeBridge.denoteSub (_equal_wd_2_0).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_2_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_1_0 := (_object_w71 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2.1 (_equal_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ)))) = (M.subValue (M.powValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (_object_w71 (M := M));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := (_object_w71 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w71 (M := M))).wd.1 ((_object_w71 (M := M))).wd.2.1 ((_object_w71 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_97 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (M.powValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

theorem h_22822 : (by
  let _chain_wd_22822_0 := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) True.intro))
  let _chain_wd_22822_1 := (let _wd_1_0 := (let _wd_2_0 := (_chain_wd_22822_0).val.argument;
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.sub _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.powNatRealInC (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.numberInC (M := M) (2 : ℂ))))
  let _chain_wd_22822_2 := _chain_wd_22822_1
  let _chain_wd_22822_3 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (144 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (144 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (144 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (144 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (144 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact ((by
    let _equal_wd_1_0 := _chain_wd_22822_0
    let _equal_wd_1_1 := _chain_wd_22822_1
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _chain_wd_22822_2
    let _equal_wd_1_1 := _chain_wd_22822_3
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _chain_wd_22822_0 := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) True.intro))
          let _chain_wd_22822_1 := (let _wd_1_0 := (let _wd_2_0 := (_chain_wd_22822_0).val.argument;
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.powNatRealInC (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.numberInC (M := M) (2 : ℂ))))
          let _chain_wd_22822_2 := _chain_wd_22822_1
          let _chain_wd_22822_3 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (144 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (144 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (144 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (144 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (144 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
          exact (And.intro (let _equal_wd_1_0 := _chain_wd_22822_0;
          let _equal_wd_1_1 := _chain_wd_22822_1;
          (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ)))) = (M.subValue (M.powValue (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from by
            have _litex_residual : (M.subValue (M.powValue (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) = (M.subValue (M.powValue (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ)))) = (M.subValue (M.powValue (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from by
            let _litex_original := _equal_wd_1_0
            let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
            let _wd_1_1 := ((_equal_wd_1_1).val.left).val.base;
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) True.intro))
            have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_97 (M := M)) (Litex.sameRefl _litex_original.val.argument)
            have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (M.powValue (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from rfl))
          ))).trans _litex_residual))) (let _equal_wd_1_0 := _chain_wd_22822_2;
          let _equal_wd_1_1 := _chain_wd_22822_3;
          (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((((17 : ℂ) / (12 : ℂ)) ^ (2 : ℕ)) - (2 : ℂ)) ((1 : ℂ) / (144 : ℂ)) (Litex.NativeBridge.denoteSub (_equal_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_1_0 := ((_equal_wd_1_0).val.left).val.base
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (144 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (144 : ℂ))) (by norm_num))))))
      )
  )

theorem h_23526 : Litex.Same (let _wd_1_0 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) True.intro)) (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.sub _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.powNatRealInC (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.numberInC (M := M) (2 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (And.left (h_22822 (M := M)))
      )
  )

theorem h_23527 : Litex.Same (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.sub _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.powNatRealInC (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (144 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (144 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (144 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (144 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (144 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) :=
  (by
    litex_complete =>
      exact (
        (And.right (h_22822 (M := M)))
      )
  )

theorem h_23528 : Litex.Same (let _wd_1_0 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) True.intro)) (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.sub _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.powNatRealInC (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.numberInC (M := M) (2 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (h_23526 (M := M))
      )
  )

theorem h_23529 : Litex.Same (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.sub _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.powNatRealInC (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (144 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (144 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (144 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (144 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (144 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) :=
  (by
    litex_complete =>
      exact (
        (h_23527 (M := M))
      )
  )

theorem h_23530 : Litex.Same (let _wd_1_0 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) True.intro)) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (144 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (144 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (144 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (144 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (144 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) :=
  (by
    litex_complete =>
      exact (
        (Eq.trans (h_23526 (M := M)) (h_23527 (M := M)))
      )
  )

theorem h_23532 : ∀ {_Host_i17 : Type v17} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_23537 : Litex.In _value_i17 (Litex.N (M := M))), (by
  let _equal_wd_1_0 := (let _object_w82 := (Litex.add _value_i17 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i17 h_23537) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _object_w82 (h_10028 (M := M)) (by
    let _atomic_wd_1_0 := _object_w82
    exact (Litex.addInN _value_i17 (Litex.number (M := M) (1 : ℂ)) h_23537 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
  let _equal_wd_1_1 := (let _object_w83 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i17 (h_10028 (M := M)) h_23537 True.intro);
  (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _object_w83 (h_7459 (M := M)) (Litex.inRPos_real _object_w83 (by
    let _atomic_wd_1_0 := _object_w83
    exact (by
      let _litex_return_call := _object_w83
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w83)).mp (by
    let _atomic_wd_1_0 := _object_w83
    exact (by
      let _litex_return_call := _object_w83
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))).2))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i17 _rep_i17 _value_i17 h_23537
          have h_23538 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i17 h_23537)
                )
            )
          have h_23682 : Litex.In _value_i17 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_23537
                )
            )
          have h_23683 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i17 h_23682)
                )
            )
          let _object_w86 := (Litex.add _value_i17 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i17 h_23682) (Litex.numberInC (M := M) (1 : ℂ)))

          have h_23533 : (by
            let _atomic_wd_1_0 := _object_w86
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w86
                    exact (by
                      let _litex_zero_bound := _atomic_wd_1_0
                      exact Litex.addPositiveRight _litex_zero_bound.val.left _litex_zero_bound.val.right _litex_zero_bound.wd.1 _litex_zero_bound.wd.2 h_23683 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))
                    ))
                )
            )
          let _object_w87 := (let _wd_1_0 := _object_w86;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w86
            exact (Litex.addInC _value_i17 _wd_1_1 (Litex.naturalToComplex _value_i17 h_23682) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))

          have h_23534 : (by
            let _equal_wd_1_0 := _object_w87
            exact Litex.Same _equal_wd_1_0 _value_i17) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w87;
                  (show Litex.Same _equal_wd_1_0 _value_i17 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i17 (Litex.naturalToComplex _value_i17 h_23682)) + (1 : ℂ)) - (1 : ℂ)) (Litex.NativeBridge.asComplex _value_i17 (Litex.naturalToComplex _value_i17 h_23682)) (Litex.NativeBridge.denoteSub (_equal_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i17 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i17 h_23682) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i17 (Litex.naturalToComplex _value_i17 h_23682)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i17 (Litex.naturalToComplex _value_i17 h_23682)) (by ring!))))
                )
            )
          let _object_w91 := (let _wd_1_0 := _object_w86;
          (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _wd_1_0 (h_10028 (M := M)) (by
            let _atomic_wd_1_0 := _object_w86
            exact (Litex.addInN _value_i17 (Litex.number (M := M) (1 : ℂ)) h_23682 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))

          let _object_w92 := (let _object_w88 := (let _wd_2_0 := _object_w87;
          (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _wd_2_0 (h_10028 (M := M)) (by
            let _atomic_wd_1_0 := _object_w87
            exact (Litex.inOfSame _value_i17 _atomic_wd_1_0 (Litex.N (M := M)) (Litex.N (M := M)) (h_23534).symm (show @Eq M.Value _ _ from Eq.refl _) h_23682)) True.intro));
          (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _object_w88 (h_7459 (M := M)) (Litex.inRPos_real _object_w88 (by
            let _atomic_wd_1_0 := _object_w88
            exact (by
              let _litex_return_call := _object_w88
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w88)).mp (by
            let _atomic_wd_1_0 := _object_w88
            exact (by
              let _litex_return_call := _object_w88
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))).2))

          have h_23535 : (by
            let _equal_wd_1_0 := _object_w91
            let _equal_wd_1_1 := _object_w92
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w91;
                  let _equal_wd_1_1 := _object_w92;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _checked_call := _equal_wd_1_0
                    have _checked_case_guard : (by
                    let _atomic_wd_1_0 := _object_w86
                    exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) := (by
                    let _atomic_wd_1_0 := _object_w86
                    exact h_23533)
                    have _selected_beta := (h_10032 (M := M)) _checked_call.val.argument _checked_call.wd.2.1 _checked_case_guard
                    exact _selected_beta.trans (show @Eq M.Value _ _ from Eq.refl _))))
                )
            )
          let _object_w93 := (_object_w92).val.argument

          let _object_w94 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i17 (h_10028 (M := M)) h_23682 True.intro)

          have h_23536 : (by
            let _equal_wd_1_0 := _object_w93
            let _equal_wd_1_1 := _object_w94
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_23534)
                )
            )
          exact (Eq.trans h_23535 (Eq.trans (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_23536) (show @Eq M.Value _ _ from Eq.refl _)))
        )
      )
  )

theorem h_25225 : ∀ {_Host_i19 : Type v19} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_25237 : Litex.In _value_i19 (Litex.RPos (M := M))), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
  let _wd_2_1 := (Litex.powNatReal _value_i19 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i19 h_25237) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
  (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_25237)
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))));
  let _wd_1_1 := (let _object_w101 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i19 (h_7459 (M := M)) (Litex.inRPos_real _value_i19 h_25237) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i19)).mp h_25237).2);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w101 (h_96 (M := M)) (by
    let _atomic_wd_1_0 := _object_w101
    exact (Litex.inRPos_real _object_w101 (Litex.callInOutput _object_w101))) True.intro));
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _litex_power := (_atomic_wd_1_0).val.right
      have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_25237)
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i19 (h_96 (M := M)) (Litex.inRPos_real _value_i19 h_25237) True.intro);
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i19 _rep_i19 _value_i19 h_25237
          have h_25238 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i19 h_25237)
                )
            )
          have h_25239 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i19 h_25238)
                )
            )
          have h_25240 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i19 h_25238) _litex_zero.symm)
                )
            )
          have h_26230 : Litex.In _value_i19 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_25237
                )
            )
          have h_26231 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i19 h_26230)
                )
            )
          have h_26232 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i19 h_26231)
                )
            )
          have h_26233 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i19 h_26231) _litex_zero.symm)
                )
            )
          have h_25226 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  h_26231
                )
            )
          have h_25227 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_26233
                )
            )
          let _object_i20 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i19 (h_7459 (M := M)) (Litex.inRPos_real _value_i19 h_26230) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i19)).mp h_26230).2)
          have h_26363 : Litex.In _object_i20 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i19 (h_7459 (M := M)) (Litex.inRPos_real _value_i19 h_26230) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i19)).mp h_26230).2)
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))
                )
            )
          have h_26364 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_i20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _object_i20 h_26363)
                )
            )
          have h_26365 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_i20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _object_i20 h_26364)
                )
            )
          have h_26366 : ¬ Litex.Same _object_i20 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _object_i20 h_26364) _litex_zero.symm)
                )
            )
          have h_26367 : Litex.Same _object_i20 _object_i20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.sameRefl (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i19 (h_7459 (M := M)) (Litex.inRPos_real _value_i19 h_26230) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i19)).mp h_26230).2))
                )
            )
          let _object_w106 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_i20 (h_96 (M := M)) (Litex.inRPos_real _object_i20 h_26363) True.intro)

          let _object_w107 := (let _wd_1_0 := (Litex.powNatReal _object_i20 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i20 h_26363) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.positiveRealToComplex _object_i20 h_26363)
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (Litex.numberInC (M := M) (2 : ℂ))))

          have h_25228 : (by
            let _equal_wd_1_0 := _object_w106
            let _equal_wd_1_1 := _object_w107
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w106;
                  let _equal_wd_1_1 := _object_w107;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _object_i20)) = (M.subValue (M.powValue (Litex.denote _object_i20) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from by
                    have _litex_residual : (M.subValue (M.powValue (Litex.denote _object_i20) (M.number (2 : ℂ))) (M.number (2 : ℂ))) = (M.subValue (M.powValue (Litex.denote _object_i20) (M.number (2 : ℂ))) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _object_i20)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _object_i20)) = (M.subValue (M.powValue (Litex.denote _object_i20) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _object_i20;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 h_26363) True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_97 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (M.powValue (Litex.denote _object_i20) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          have h_25229 : (by
            let _chain_wd_25229_0 := (let _wd_1_0 := _object_i20;
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
              let _atomic_wd_1_0 := _object_i20
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) True.intro))
            let _chain_wd_25229_1 := _object_w106
            let _chain_wd_25229_2 := _object_w106
            let _chain_wd_25229_3 := _object_w107
            let _chain_wd_25229_4 := _object_w107
            let _chain_wd_25229_5 := (let _wd_1_0 := (let _wd_2_0 := _object_i20;
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_i20
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.sub _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              )) (Litex.numberInC (M := M) (2 : ℂ))))
            exact ((by
              let _equal_wd_1_0 := _chain_wd_25229_0
              let _equal_wd_1_1 := _chain_wd_25229_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
              let _equal_wd_1_0 := _chain_wd_25229_2
              let _equal_wd_1_1 := _chain_wd_25229_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_25229_4
              let _equal_wd_1_1 := _chain_wd_25229_5
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_25229_0 := (let _wd_1_0 := _object_i20;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
                      let _atomic_wd_1_0 := _object_i20
                      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) True.intro))
                    let _chain_wd_25229_1 := _object_w106
                    let _chain_wd_25229_2 := _object_w106
                    let _chain_wd_25229_3 := _object_w107
                    let _chain_wd_25229_4 := _object_w107
                    let _chain_wd_25229_5 := (let _wd_1_0 := (let _wd_2_0 := _object_i20;
                    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _object_i20
                      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.sub _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                      )) (Litex.numberInC (M := M) (2 : ℂ))))
                    exact (And.intro (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_26367).symm) (And.intro h_25228 (congrArg₂ M.subValue (show (M.powValue (Litex.denote _object_i20) (M.number (2 : ℂ))) = (M.powValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (2 : ℂ))) from (congrArg₂ M.powValue (show (Litex.denote _object_i20) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) from h_26367) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _))))))
                )
            )

          have h_28068 :=
            (And.left h_25229)

          have h_28069 :=
            (And.left (And.right h_25229))

          have h_28070 :=
            (And.right (And.right h_25229))

          have h_28071 :=
            h_28068

          have h_28072 :=
            h_28069

          have h_28073 :=
            h_28070

          have h_28315 : Litex.Same (_object_w107).val.left (let _wd_1_0 := _object_i20;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _object_i20
            exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.subCancelRightRight (_object_w107).val.left (let _wd_1_0 := _object_i20;
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_i20
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.number (M := M) (2 : ℂ)) (by
                    let _atomic_wd_1_0 := (_object_w107).val.left
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.positiveRealToComplex _object_i20 h_26363)
                      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                    )) (by
                    let _atomic_wd_1_0 := (let _wd_1_0 := _object_i20;
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_2_0 := _object_i20
                      exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.inOfSame _object_i20 _atomic_wd_2_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))
                      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                    )) (Litex.numberInC (M := M) (2 : ℂ)) h_28073)
                )
            )

          have h_28316 :=
            (Eq.trans h_28068 h_28069)

          have h_28317 :=
            (Eq.trans (Eq.trans h_28068 h_28069) h_28070)

          have h_28318 :=
            (Eq.trans h_28069 h_28070)
          let _object_w112 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i19 (h_96 (M := M)) (Litex.inRPos_real _value_i19 h_26230) True.intro)

          let _object_w113 := (let _wd_1_0 := (Litex.powNatReal _value_i19 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i19 h_26230) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_26230)
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (Litex.numberInC (M := M) (2 : ℂ))))

          have h_25230 : (by
            let _equal_wd_1_0 := _object_w112
            let _equal_wd_1_1 := _object_w113
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w112;
                  let _equal_wd_1_1 := _object_w113;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i19)) = (M.subValue (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from by
                    have _litex_residual : (M.subValue (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ))) (M.number (2 : ℂ))) = (M.subValue (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ))) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i19)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i19)) = (M.subValue (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i19;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 h_26230) True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_97 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w114 := (let _wd_1_0 := (let _wd_2_0 := _value_i19;
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_26230) h_26233);
          (Litex.add _wd_2_0 _wd_2_1 (Litex.positiveRealToComplex _wd_2_0 h_26230) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_26230) (_atomic_wd_1_0).wd.2.2))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i19 (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex _value_i19 h_26230) (Litex.divInC _wd_1_1 _value_i19 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i19 h_26230) ((_atomic_wd_1_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

          have h_25231 : (by
            let _equal_wd_1_0 := _object_i20
            let _equal_wd_1_1 := _object_w114
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) = (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) from by
                    have _litex_residual : (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) = (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) = (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) from by
                    let _litex_original := _object_i20
                    let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
                    let _wd_1_1 := _value_i19;
                    (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 h_26230) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp h_26230).2))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_7460 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w115 := (let _wd_1_0 := (let _wd_2_0 := _object_w114;
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _object_w114
            exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) ((h_26367).trans h_25231) (show @Eq M.Value _ _ from Eq.refl _) h_26363))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) ((h_26367).trans h_25231) (show @Eq M.Value _ _ from Eq.refl _) h_26363))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (Litex.numberInC (M := M) (2 : ℂ))))

          have h_25232 : (by
            let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _object_i20;
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_i20
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.sub _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              )) (Litex.numberInC (M := M) (2 : ℂ))))
            let _equal_wd_1_1 := _object_w115
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ M.subValue (show (M.powValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (2 : ℂ))) = (M.powValue (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from (congrArg₂ M.powValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) = (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) from h_25231) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )

          have h_33441 : Litex.Same (let _wd_1_0 := _object_i20;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _object_i20
            exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (_object_w115).val.left :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.subCancelRightRight (let _wd_1_0 := _object_i20;
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_i20
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (_object_w115).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _atomic_wd_1_0 := (let _wd_1_0 := _object_i20;
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _object_i20
                      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.positiveRealToComplex _object_i20 (Litex.inOfSame _object_i20 _object_i20 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))
                      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                    )) (by
                    let _atomic_wd_1_0 := (_object_w115).val.left
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) ((h_26367).trans h_25231) (show @Eq M.Value _ _ from Eq.refl _) h_26363))
                      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                    )) (Litex.numberInC (M := M) (2 : ℂ)) h_25232)
                )
            )
          have h_25233 : (by
            let _chain_wd_25233_0 := (let _wd_1_0 := _object_i20;
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
              let _atomic_wd_1_0 := _object_i20
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) True.intro))
            let _chain_wd_25233_1 := (let _wd_1_0 := (let _wd_2_0 := _object_i20;
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_i20
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.sub _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              )) (Litex.numberInC (M := M) (2 : ℂ))))
            let _chain_wd_25233_2 := _chain_wd_25233_1
            let _chain_wd_25233_3 := _object_w115
            exact ((by
              let _equal_wd_1_0 := _chain_wd_25233_0
              let _equal_wd_1_1 := _chain_wd_25233_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_25233_2
              let _equal_wd_1_1 := _chain_wd_25233_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_25233_0 := (let _wd_1_0 := _object_i20;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
                      let _atomic_wd_1_0 := _object_i20
                      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) True.intro))
                    let _chain_wd_25233_1 := (let _wd_1_0 := (let _wd_2_0 := _object_i20;
                    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _object_i20
                      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.sub _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                      )) (Litex.numberInC (M := M) (2 : ℂ))))
                    let _chain_wd_25233_2 := _chain_wd_25233_1
                    let _chain_wd_25233_3 := _object_w115
                    exact (And.intro h_28317 h_25232))
                )
            )

          have h_33446 :=
            (And.left h_25233)

          have h_33447 :=
            (And.right h_25233)

          have h_33448 :=
            h_33446

          have h_33449 :=
            h_33447

          have h_33450 :=
            (Eq.trans h_33446 h_33447)
          let _object_w117 := (let _wd_1_0 := _object_w112;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _object_w112
            exact (by
              let _litex_return_call := _object_w112
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

          let _object_w118 := (let _wd_1_0 := _object_w113;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _object_w113
            exact (Litex.subInR (_object_w113).val.left _wd_1_1 (by
              let _litex_power := (_object_w113).val.left
              have _elaborated_power_base := (Litex.inRPos_real _value_i19 h_26230)
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInR _litex_power _recorded_power_base
            ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

          have h_25234 : (by
            let _equal_wd_1_0 := _object_w117
            let _equal_wd_1_1 := _object_w118
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ M.powValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i19)) = (M.subValue (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from h_25230) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          let _object_w119 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_2_1 := (_object_w113).val.left;
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_26230)
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))));
          let _wd_1_1 := _object_w115;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _litex_power := (_atomic_wd_1_0).val.right
              have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_26230)
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))) (by
            let _atomic_wd_1_0 := _object_w115
            exact (Litex.subInC (_object_w115).val.left (Litex.number (M := M) (2 : ℂ)) (by
              let _litex_power := (_object_w115).val.left
              have _elaborated_power_base := (Litex.positiveRealToComplex ((_object_w115).val.left).val.base (Litex.inOfSame _object_i20 ((_object_w115).val.left).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) ((h_26367).trans h_25231) (show @Eq M.Value _ _ from Eq.refl _) h_26363))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ) (Litex.numberInC (M := M) (2 : ℂ))))))

          have h_25235 : (by
            let _equal_wd_1_0 := _object_w119
            let _equal_wd_1_1 := _object_w118
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w119;
                  let _equal_wd_1_1 := _object_w118;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((4 : ℂ) * ((Litex.NativeBridge.asComplex _value_i19 (Litex.positiveRealToComplex _value_i19 h_26230)) ^ (2 : ℕ))) * (((((Litex.NativeBridge.asComplex _value_i19 (Litex.positiveRealToComplex _value_i19 h_26230)) + ((2 : ℂ) / (Litex.NativeBridge.asComplex _value_i19 (Litex.positiveRealToComplex _value_i19 h_26230)))) / (2 : ℂ)) ^ (2 : ℕ)) - (2 : ℂ))) ((((Litex.NativeBridge.asComplex _value_i19 (Litex.positiveRealToComplex _value_i19 h_26230)) ^ (2 : ℕ)) - (2 : ℂ)) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) ((_equal_wd_1_0).val.left).val.right ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denotePowNatReal _value_i19 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i19 h_26230) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i19 (Litex.positiveRealToComplex _value_i19 h_26230)))) (Litex.NativeBridge.denoteSub (_object_w115).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w115).wd.1 (_object_w115).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_object_w115).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_w114
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) ((h_26367).trans h_25231) (show @Eq M.Value _ _ from Eq.refl _) h_26363))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (_object_w114).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w114).wd.1 (_object_w114).wd.2.1 (_object_w114).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i19 ((_object_w114).val.left).val.right ((_object_w114).val.left).wd.1 ((_object_w114).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i19 (Litex.positiveRealToComplex _value_i19 h_26230)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) _value_i19 (((_object_w114).val.left).val.right).wd.1 (((_object_w114).val.left).val.right).wd.2.1 (((_object_w114).val.left).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i19 (Litex.positiveRealToComplex _value_i19 h_26230)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denotePowNatReal (_object_w118).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_w113
                    exact (Litex.subInR (_object_w113).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w113).val.left
                      have _elaborated_power_base := (Litex.inRPos_real _value_i19 h_26230)
                      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInR _litex_power _recorded_power_base
                    ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub (_object_w113).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w113).wd.1 (_object_w113).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal _value_i19 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i19 h_26230) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i19 (Litex.positiveRealToComplex _value_i19 h_26230))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i19 (Litex.positiveRealToComplex _value_i19 h_26230)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i19 (Litex.NativeBridge.asComplex _value_i19 (Litex.positiveRealToComplex _value_i19 h_26230)) (Litex.NativeBridge.asComplex_spec _value_i19 (Litex.positiveRealToComplex _value_i19 h_26230)) h_26233
                    have _litex_nz_1 : ((2 : ℂ) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | exact _litex_nz_1 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          have h_25236 : (by
            let _chain_wd_25236_0 := (let _wd_1_0 := (_object_w119).val.left;
            let _wd_1_1 := (let _wd_1_0 := _object_i20;
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
              let _atomic_wd_1_0 := _object_i20
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) True.intro));
            (Litex.mul _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _litex_power := (_atomic_wd_1_0).val.right
                have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_26230)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_i20 (h_96 (M := M)) (by
                let _atomic_wd_1_0 := _object_i20
                exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) True.intro) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_i20 (h_96 (M := M)) (by
                let _atomic_wd_1_0 := _object_i20
                exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) True.intro))))))
            let _chain_wd_25236_1 := _object_w119
            let _chain_wd_25236_2 := _object_w119
            let _chain_wd_25236_3 := _object_w118
            let _chain_wd_25236_4 := _object_w118
            let _chain_wd_25236_5 := _object_w117
            exact ((by
              let _equal_wd_1_0 := _chain_wd_25236_0
              let _equal_wd_1_1 := _chain_wd_25236_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
              let _equal_wd_1_0 := _chain_wd_25236_2
              let _equal_wd_1_1 := _chain_wd_25236_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_25236_4
              let _equal_wd_1_1 := _chain_wd_25236_5
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_25236_0 := (let _wd_1_0 := (_object_w119).val.left;
                    let _wd_1_1 := (let _wd_1_0 := _object_i20;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
                      let _atomic_wd_1_0 := _object_i20
                      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) True.intro));
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                        let _litex_power := (_atomic_wd_1_0).val.right
                        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_26230)
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                      ))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_i20 (h_96 (M := M)) (by
                        let _atomic_wd_1_0 := _object_i20
                        exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) True.intro) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_i20 (h_96 (M := M)) (by
                        let _atomic_wd_1_0 := _object_i20
                        exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_26367 (show @Eq M.Value _ _ from Eq.refl _) h_26363))) True.intro))))))
                    let _chain_wd_25236_1 := _object_w119
                    let _chain_wd_25236_2 := _object_w119
                    let _chain_wd_25236_3 := _object_w118
                    let _chain_wd_25236_4 := _object_w118
                    let _chain_wd_25236_5 := _object_w117
                    exact (And.intro (congrArg₂ M.mulValue (show (M.mulValue (M.number (4 : ℂ)) (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ)))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ)))) from (show @Eq M.Value _ _ from Eq.refl _)) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19))) = (M.subValue (M.powValue (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from h_33450)) (And.intro h_25235 (h_25234).symm)))
                )
            )

          have h_42816 :=
            (And.left h_25236)

          have h_42817 :=
            (And.left (And.right h_25236))

          have h_42818 :=
            (And.right (And.right h_25236))

          have h_42819 :=
            h_42816

          have h_42820 :=
            h_42817

          have h_42821 :=
            h_42818

          have h_48398 :=
            (Eq.trans h_42816 h_42817)

          have h_48399 :=
            (Eq.trans (Eq.trans h_42816 h_42817) h_42818)

          have h_48400 :=
            (Eq.trans h_42817 h_42818)
          exact h_48399
        )
      )
  )

theorem h_49396 : ∀ {_Host_i22 : Type v22} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (h_49410 : Litex.In _value_i22 (Litex.RPos (M := M))), (by
  let _atomic_wd_1_0 := (let _object_w127 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_49410) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_49410).2);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w127 (h_96 (M := M)) (by
    let _atomic_wd_2_0 := _object_w127
    exact (Litex.inRPos_real _object_w127 (Litex.callInOutput _object_w127))) True.intro))
  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i22 _rep_i22 _value_i22 h_49410
          have h_49411 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i22 h_49410)
                )
            )
          have h_49412 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i22 h_49411)
                )
            )
          have h_49413 : ¬ Litex.Same _value_i22 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i22 h_49411) _litex_zero.symm)
                )
            )
          have h_49806 : Litex.In _value_i22 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_49410
                )
            )
          have h_49807 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i22 h_49806)
                )
            )
          have h_49808 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i22 h_49807)
                )
            )
          have h_49809 : ¬ Litex.Same _value_i22 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i22 h_49807) _litex_zero.symm)
                )
            )
          have h_49811 : Litex.Same (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_49806) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))));
          let _wd_1_1 := (let _object_w133 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_49806) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_49806).2);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w133 (h_96 (M := M)) (by
            let _atomic_wd_1_0 := _object_w133
            exact (Litex.inRPos_real _object_w133 (Litex.callInOutput _object_w133))) True.intro));
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _litex_power := (_atomic_wd_1_0).val.right
              have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))))) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_49806) True.intro);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_49810 : Litex.In _value_i22 (Litex.RPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_49806
                          )
                      )
                    have h_49816 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i22 h_49810)
                          )
                      )
                    have h_49817 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i22 h_49816)
                          )
                      )
                    have h_49818 : ¬ Litex.Same _value_i22 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i22 h_49816) _litex_zero.symm)
                          )
                      )
                    exact ((h_25225 (M := M)) _value_i22 h_49810)
                  )
                )
            )
          have h_49397 : (by
            let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
            let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_49806) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := _wd_2_1
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              ))));
            let _wd_1_1 := (let _object_w133 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_49806) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_49806).2);
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w133 (h_96 (M := M)) (by
              let _atomic_wd_1_0 := _object_w133
              exact (Litex.inRPos_real _object_w133 (Litex.callInOutput _object_w133))) True.intro));
            (Litex.mul _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _litex_power := (_atomic_wd_1_0).val.right
                have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
            let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_49806) True.intro);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_49811
                )
            )
          let _object_w137 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_49806) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))

          have h_49398 : (by
            let _atomic_wd_1_0 := _object_w137
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w137
                    exact (by
                      let _atomic_wd_2_1 := _atomic_wd_1_0
                      exact (Litex.powStructuralPositiveOfEven _atomic_wd_2_1 (Litex.inRPos_real _value_i22 h_49806) (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num) (by norm_num) h_49809)))
                )
            )
          let _object_w138 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_1_1 := _object_w137;
          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _object_w137
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))))

          have h_49399 : (by
            let _atomic_wd_1_0 := _object_w138
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w138
                    exact (by
                      let _litex_positive_result := _atomic_wd_1_0
                      exact Litex.mulPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (by
                      let _atomic_wd_2_1 := _object_w137
                      exact h_49398)
                    ))
                )
            )
          have h_49400 : (by
            let _atomic_wd_1_0 := _object_w138
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w138
                    exact (fun _litex_equal => (Litex.ltNotSame (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0 h_49399) _litex_equal.symm))
                )
            )
          have h_49401 : (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_49806) True.intro);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_49806) True.intro);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_return_call := _atomic_wd_1_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    exact (by
                      let _atomic_wd_2_1 := _atomic_wd_1_0
                      exact (Litex.powStructuralNonnegativeOfEven _atomic_wd_2_1 (by
                        let _atomic_wd_3_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_49806) True.intro)
                        exact (by
                          let _litex_return_call := _atomic_wd_3_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num))))
                )
            )
          have h_49402 : (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
            let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_49806) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := _wd_2_1
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              ))));
            let _wd_1_1 := (let _object_w133 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_49806) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_49806).2);
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w133 (h_96 (M := M)) (by
              let _atomic_wd_1_0 := _object_w133
              exact (Litex.inRPos_real _object_w133 (Litex.callInOutput _object_w133))) True.intro));
            (Litex.mul _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _litex_power := (_atomic_wd_1_0).val.right
                have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
                    let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_49806) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                      ))));
                    let _wd_1_1 := (let _object_w133 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_49806) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_49806).2);
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w133 (h_96 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w133
                      exact (Litex.inRPos_real _object_w133 (Litex.callInOutput _object_w133))) True.intro));
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                        let _litex_power := (_atomic_wd_1_0).val.right
                        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                      ))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
                    exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_49806) True.intro);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_return_call := _atomic_wd_1_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) _atomic_wd_1_0 (show @Eq M.Value _ _ from Eq.refl _) (h_49811).symm h_49401))
                )
            )
          let _object_w162 := (let _object_w161 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_49806) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_49806).2);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w161 (h_96 (M := M)) (by
            let _atomic_wd_1_0 := _object_w161
            exact (Litex.inRPos_real _object_w161 (Litex.callInOutput _object_w161))) True.intro))

          have h_49403 : (by
            let _atomic_wd_1_0 := _object_w162
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w162
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
                )
            )
          have h_49404 : (by
            let _atomic_wd_1_0 := _object_w137
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w137
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.inRPos_real _value_i22 h_49806)
                      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInR _litex_power _recorded_power_base
                    ))
                )
            )
          have h_49405 : (by
            let _atomic_wd_1_0 := _object_w138
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w138
                    exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) (_object_w138).val.right (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) h_49404))
                )
            )
          have h_49406 : (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
            let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_49806) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := _wd_2_1
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              ))));
            let _wd_1_1 := (let _object_w133 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_49806) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_49806).2);
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w133 (h_96 (M := M)) (by
              let _atomic_wd_1_0 := _object_w133
              exact (Litex.inRPos_real _object_w133 (Litex.callInOutput _object_w133))) True.intro));
            (Litex.mul _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _litex_power := (_atomic_wd_1_0).val.right
                have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
                    let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_49806) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                      ))));
                    let _wd_1_1 := (let _object_w133 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_49806) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_49806).2);
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w133 (h_96 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w133
                      exact (Litex.inRPos_real _object_w133 (Litex.callInOutput _object_w133))) True.intro));
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                        let _litex_power := (_atomic_wd_1_0).val.right
                        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                      ))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
                    exact (Litex.mulInR _object_w138 _object_w162 h_49405 h_49403))
                )
            )
          let _object_w164 := (let _wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_49806) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))));
          let _wd_1_1 := (let _object_w133 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_49806) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_49806).2);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w133 (h_96 (M := M)) (by
            let _atomic_wd_1_0 := _object_w133
            exact (Litex.inRPos_real _object_w133 (Litex.callInOutput _object_w133))) True.intro));
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _litex_power := (_atomic_wd_1_0).val.right
              have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_49806)
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))));
          let _wd_1_1 := _object_w138;
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (M.real_subset_complex _ h_49406)) (by
            let _atomic_wd_1_0 := _object_w138
            exact (M.real_subset_complex _ h_49405)) (by
            let _atomic_wd_1_0 := _object_w138
            exact h_49400)))

          have h_49407 : (by
            let _atomic_wd_1_0 := _object_w164
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w164
                    exact (Litex.divInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right h_49406 h_49405 (_atomic_wd_1_0).wd.2.2))
                )
            )
          have h_49408 : (by
            let _atomic_wd_1_0 := _object_w164
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w164
                    exact (Litex.divStructuralNonnegative _atomic_wd_1_0 (by
                      let _atomic_wd_2_1 := _object_w138
                      exact h_49399) (by
                      let _atomic_wd_2_1 := (_object_w164).val.left
                      exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_49806) True.intro);
                      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                      (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (by
                          let _litex_return_call := _atomic_wd_1_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (h_49811).symm h_49401))))
                )
            )
          have h_49409 : (by
            let _chain_wd_49409_0 := _object_w162
            let _chain_wd_49409_1 := _object_w164
            exact ((by
              let _equal_wd_1_0 := _chain_wd_49409_0
              let _equal_wd_1_1 := _chain_wd_49409_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _atomic_wd_1_0 := _object_w164
              exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_49409_0 := _object_w162
                    let _chain_wd_49409_1 := _object_w164
                    exact (And.intro (let _equal_wd_1_0 := _chain_wd_49409_0;
                    let _equal_wd_1_1 := _chain_wd_49409_1;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                      let _quotient := _equal_wd_1_1
                      let _product := (_object_w164).val.left
                      have _child : (by
                        let _equal_wd_2_0 := (_object_w164).val.left
                        let _equal_wd_2_1 := _equal_wd_2_0
                        exact Litex.Same _equal_wd_2_1 _equal_wd_2_1) := (show @Eq M.Value _ _ from Eq.refl _)
                      have _conversion := Litex.sameDivIffSameMul _quotient.val.left _quotient.val.right _product.val.right _quotient.wd.1 _quotient.wd.2.1 _product.wd.2 _quotient.wd.2.2
                      exact ((_conversion.mpr (_child.trans (Litex.sameMulComm _product.val.left _product.val.right _product.wd.1 _product.wd.2))).symm)))) (by
                      let _atomic_wd_1_0 := _object_w164
                      exact h_49408)))
                )
            )

          have h_69507 :=
            (And.left h_49409)

          have h_69508 :=
            (And.right h_49409)

          have h_69509 :=
            h_69507

          have h_69510 :=
            h_69508

          have h_69780 :=
            (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w164 _object_w162 (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (Eq.symm h_69507) h_69508)
          exact (by
            let _atomic_wd_1_0 := _object_w162
            exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w164 _atomic_wd_1_0 (show @Eq M.Value _ _ from Eq.refl _) (h_69507).symm h_49408))
        )
      )
  )

theorem h_70186 : ∀ {_Host_i24 : Type v24} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (h_70195 : Litex.In _value_i24 (Litex.RPos (M := M))), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
  let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_70195) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
  (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_70195)
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))));
  let _wd_1_1 := (let _wd_2_0 := (let _object_w171 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_70195) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_70195).2);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w171 (h_96 (M := M)) (by
    let _atomic_wd_1_0 := _object_w171
    exact (Litex.inRPos_real _object_w171 (Litex.callInOutput _object_w171))) True.intro));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _litex_power := (_atomic_wd_1_0).val.right
      have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_70195)
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (by
      let _litex_abs := _atomic_wd_1_0
      exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
    )))))
  let _equal_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_70195) True.intro);
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_abs := _atomic_wd_1_0
      exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
    )) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i24 _rep_i24 _value_i24 h_70195
          have h_70196 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i24 h_70195)
                )
            )
          have h_70197 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i24 h_70196)
                )
            )
          have h_70198 : ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i24 h_70196) _litex_zero.symm)
                )
            )
          have h_71801 : Litex.In _value_i24 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_70195
                )
            )
          have h_71802 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i24 h_71801)
                )
            )
          have h_71803 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i24 h_71802)
                )
            )
          have h_71804 : ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i24 h_71802) _litex_zero.symm)
                )
            )
          have h_71806 : Litex.Same (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_71801) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71801)
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))));
          let _wd_1_1 := (let _object_w179 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w179 (h_96 (M := M)) (by
            let _atomic_wd_1_0 := _object_w179
            exact (Litex.inRPos_real _object_w179 (Litex.callInOutput _object_w179))) True.intro));
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _litex_power := (_atomic_wd_1_0).val.right
              have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71801)
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))))) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_71801) True.intro);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_71805 : Litex.In _value_i24 (Litex.RPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_71801
                          )
                      )
                    have h_71811 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i24 h_71805)
                          )
                      )
                    have h_71812 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i24 h_71811)
                          )
                      )
                    have h_71813 : ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i24 h_71811) _litex_zero.symm)
                          )
                      )
                    exact ((h_25225 (M := M)) _value_i24 h_71805)
                  )
                )
            )
          have h_70187 : (by
            let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
            let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_71801) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := _wd_2_1
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71801)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              ))));
            let _wd_1_1 := (let _object_w179 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2);
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w179 (h_96 (M := M)) (by
              let _atomic_wd_1_0 := _object_w179
              exact (Litex.inRPos_real _object_w179 (Litex.callInOutput _object_w179))) True.intro));
            (Litex.mul _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _litex_power := (_atomic_wd_1_0).val.right
                have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71801)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
            let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_71801) True.intro);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_71806
                )
            )
          have h_78502 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (let _object_w186 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w186 (h_96 (M := M)) (by
            let _atomic_wd_1_0 := _object_w186
            exact (Litex.inRPos_real _object_w186 (Litex.callInOutput _object_w186))) True.intro)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_78501 : Litex.In _value_i24 (Litex.RPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_71801
                          )
                      )
                    have h_78507 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i24 h_78501)
                          )
                      )
                    have h_78508 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i24 h_78507)
                          )
                      )
                    have h_78509 : ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i24 h_78507) _litex_zero.symm)
                          )
                      )
                    exact ((h_49396 (M := M)) _value_i24 h_78501)
                  )
                )
            )
          have h_70188 : (by
            let _atomic_wd_1_0 := (let _object_w186 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2);
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w186 (h_96 (M := M)) (by
              let _atomic_wd_1_0 := _object_w186
              exact (Litex.inRPos_real _object_w186 (Litex.callInOutput _object_w186))) True.intro))
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _object_w186 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2);
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w186 (h_96 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w186
                      exact (Litex.inRPos_real _object_w186 (Litex.callInOutput _object_w186))) True.intro))
                    exact h_78502)
                )
            )
          have h_70189 : (by
            let _atomic_wd_1_0 := (let _object_w186 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2);
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w186 (h_96 (M := M)) (by
              let _atomic_wd_1_0 := _object_w186
              exact (Litex.inRPos_real _object_w186 (Litex.callInOutput _object_w186))) True.intro))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _object_w186 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2);
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w186 (h_96 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w186
                      exact (Litex.inRPos_real _object_w186 (Litex.callInOutput _object_w186))) True.intro))
                    exact (by
                      let _litex_return_call := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2) (h_96 (M := M)) (by
                      let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2)
                      exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2)))) True.intro)
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
                )
            )
          have h_70190 : (by
            let _atomic_wd_1_1 := (let _object_w186 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2);
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w186 (h_96 (M := M)) (by
              let _atomic_wd_1_0 := _object_w186
              exact (Litex.inRPos_real _object_w186 (Litex.callInOutput _object_w186))) True.intro))
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _object_w186 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2);
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w186 (h_96 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w186
                      exact (Litex.inRPos_real _object_w186 (Litex.callInOutput _object_w186))) True.intro))
                    exact h_78502)
                )
            )
          let _object_w189 := (let _wd_1_0 := (let _object_w186 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w186 (h_96 (M := M)) (by
            let _atomic_wd_1_0 := _object_w186
            exact (Litex.inRPos_real _object_w186 (Litex.callInOutput _object_w186))) True.intro));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact h_70189)))

          have h_70191 : (by
            let _equal_wd_1_0 := _object_w189
            let _equal_wd_1_1 := (_equal_wd_1_0).val.arg
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w189;
                  let _equal_wd_1_1 := (_equal_wd_1_0).val.arg;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _litex_abs := _equal_wd_1_0
                    exact (Litex.absOfNonnegative _litex_abs.val.arg _litex_abs.wd (by
                    let _atomic_wd_1_1 := _equal_wd_1_1
                    exact h_70190))
                  )))
                )
            )
          let _object_w190 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_71801) True.intro)

          have h_70192 : (by
            let _atomic_wd_1_0 := _object_w190
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w190
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
                )
            )
          let _object_w191 := (let _wd_1_0 := (let _wd_2_0 := _object_w190;
          (Litex.abs _wd_2_0 (by
            let _atomic_wd_1_0 := _object_w190
            exact h_70192)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_abs := _atomic_wd_1_0
              exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
            )) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

          have h_70193 : (by
            let _equal_wd_1_0 := _object_w191
            let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_71801) True.intro);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w191;
                  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_71801) True.intro);
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _litex_abs_power := _equal_wd_1_0
                    let _litex_argument_power := _equal_wd_1_1
                    exact (Litex.absPowStructuralSame _litex_abs_power _litex_argument_power (2 : ℕ) (Litex.sameRefl _litex_abs_power.val.base.val.arg) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num))
                  )))
                )
            )
          have h_70194 : (by
            let _chain_wd_70194_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
            let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_71801) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := _wd_2_1
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71801)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              ))));
            let _wd_1_1 := _object_w189;
            (Litex.mul _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _litex_power := (_atomic_wd_1_0).val.right
                have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71801)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := _object_w189
              exact (M.real_subset_complex _ (Litex.inOfSame (_object_w189).val.arg _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_70191).symm (show @Eq M.Value _ _ from Eq.refl _) h_70189)))))
            let _chain_wd_70194_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
            let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_71801) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := _wd_2_1
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71801)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              ))));
            let _wd_1_1 := (let _object_w179 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2);
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w179 (h_96 (M := M)) (by
              let _atomic_wd_1_0 := _object_w179
              exact (Litex.inRPos_real _object_w179 (Litex.callInOutput _object_w179))) True.intro));
            (Litex.mul _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _litex_power := (_atomic_wd_1_0).val.right
                have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71801)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
            let _chain_wd_70194_2 := _chain_wd_70194_1
            let _chain_wd_70194_3 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_71801) True.intro);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            let _chain_wd_70194_4 := _chain_wd_70194_3
            let _chain_wd_70194_5 := _object_w191
            exact ((by
              let _equal_wd_1_0 := _chain_wd_70194_0
              let _equal_wd_1_1 := _chain_wd_70194_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
              let _equal_wd_1_0 := _chain_wd_70194_2
              let _equal_wd_1_1 := _chain_wd_70194_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_70194_4
              let _equal_wd_1_1 := _chain_wd_70194_5
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_70194_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
                    let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_71801) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71801)
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                      ))));
                    let _wd_1_1 := _object_w189;
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                        let _litex_power := (_atomic_wd_1_0).val.right
                        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71801)
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                      ))) (by
                      let _atomic_wd_1_0 := _object_w189
                      exact (M.real_subset_complex _ (Litex.inOfSame (_object_w189).val.arg _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_70191).symm (show @Eq M.Value _ _ from Eq.refl _) h_70189)))))
                    let _chain_wd_70194_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
                    let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_71801) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71801)
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                      ))));
                    let _wd_1_1 := (let _object_w179 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71801) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71801).2);
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w179 (h_96 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w179
                      exact (Litex.inRPos_real _object_w179 (Litex.callInOutput _object_w179))) True.intro));
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                        let _litex_power := (_atomic_wd_1_0).val.right
                        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71801)
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                      ))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
                    let _chain_wd_70194_2 := _chain_wd_70194_1
                    let _chain_wd_70194_3 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_71801) True.intro);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_return_call := _atomic_wd_1_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    let _chain_wd_70194_4 := _chain_wd_70194_3
                    let _chain_wd_70194_5 := _object_w191
                    exact (And.intro (congrArg₂ M.mulValue (show (M.mulValue (M.number (4 : ℂ)) (M.powValue (Litex.denote _value_i24) (M.number (2 : ℂ)))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (Litex.denote _value_i24) (M.number (2 : ℂ)))) from (show @Eq M.Value _ _ from Eq.refl _)) (show (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i24)))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i24))) from h_70191)) (And.intro h_71806 (h_70193).symm)))
                )
            )

          have h_83379 :=
            (And.left h_70194)

          have h_83380 :=
            (And.left (And.right h_70194))

          have h_83381 :=
            (And.right (And.right h_70194))

          have h_83382 :=
            h_83379

          have h_83383 :=
            h_83380

          have h_83384 :=
            h_83381

          have h_86841 :=
            (Eq.trans h_83379 h_83380)

          have h_86842 :=
            (Eq.trans (Eq.trans h_83379 h_83380) h_83381)

          have h_86843 :=
            (Eq.trans h_83380 h_83381)
          exact h_86842
        )
      )
  )

theorem h_88452 : ∀ {_Host_i26 : Type v26} [_rep_i26 : Litex.Representation M _Host_i26] (_value_i26 : Litex.Obj (M := M) _Host_i26) (h_88465 : Litex.In _value_i26 (Litex.RPos (M := M))), (by
  let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i26 (h_7459 (M := M)) (Litex.inRPos_real _value_i26 h_88465) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i26)).mp h_88465).2)
  exact Litex.Lt (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i26 _rep_i26 _value_i26 h_88465
          have h_88466 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i26 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i26 h_88465)
                )
            )
          have h_88467 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i26 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i26 h_88466)
                )
            )
          have h_88468 : ¬ Litex.Same _value_i26 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i26 h_88466) _litex_zero.symm)
                )
            )
          have h_88614 : Litex.In _value_i26 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_88465
                )
            )
          have h_88615 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i26 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i26 h_88614)
                )
            )
          have h_88616 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i26 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i26 h_88615)
                )
            )
          have h_88617 : ¬ Litex.Same _value_i26 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i26 h_88615) _litex_zero.symm)
                )
            )
          have h_88453 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i26 :=
            (by
              litex_checked_step =>
                exact (
                  h_88615
                )
            )
          have h_88454 : ¬ Litex.Same _value_i26 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_88617
                )
            )
          let _object_w203 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i26 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i26 h_88614))

          have h_88455 : (by
            let _atomic_wd_1_0 := _object_w203
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w203
                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614))) (0 : ℂ) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i26 (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (mul_ne_zero (Litex.NativeBridge.nativeNonzeroOfDenote (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (Litex.NativeBridge.nativeNonzeroOfDenote _value_i26 (Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614)) (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614)) h_88617))))
                )
            )
          let _object_w204 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i26 (h_7459 (M := M)) (Litex.inRPos_real _value_i26 h_88614) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i26)).mp h_88614).2)

          let _object_w205 := (let _wd_1_0 := (let _wd_2_0 := _value_i26;
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_88614) h_88617);
          (Litex.add _wd_2_0 _wd_2_1 (Litex.positiveRealToComplex _wd_2_0 h_88614) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_88614) (_atomic_wd_1_0).wd.2.2))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i26 (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex _value_i26 h_88614) (Litex.divInC _wd_1_1 _value_i26 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i26 h_88614) ((_atomic_wd_1_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

          have h_88456 : (by
            let _equal_wd_1_0 := _object_w204
            let _equal_wd_1_1 := _object_w205
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w204;
                  let _equal_wd_1_1 := _object_w205;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i26)) = (M.divValue (M.addValue (Litex.denote _value_i26) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i26))) (M.number (2 : ℂ))) from by
                    have _litex_residual : (M.divValue (M.addValue (Litex.denote _value_i26) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i26))) (M.number (2 : ℂ))) = (M.divValue (M.addValue (Litex.denote _value_i26) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i26))) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i26)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i26)) = (M.divValue (M.addValue (Litex.denote _value_i26) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i26))) (M.number (2 : ℂ))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
                    let _wd_1_1 := _value_i26;
                    (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 h_88614) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp h_88614).2))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_7460 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i26) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i26))) (M.number (2 : ℂ))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w206 := (let _wd_1_0 := _object_w204;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w204
            exact (Litex.positiveRealToComplex _object_w204 (Litex.callInOutput _object_w204))) (Litex.numberInC (M := M) (1 : ℂ))))

          let _object_w207 := (let _wd_1_0 := _object_w205;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w205
            exact (Litex.divInC (_object_w205).val.left (Litex.number (M := M) (2 : ℂ)) (Litex.addInC _value_i26 ((_object_w205).val.left).val.right (Litex.positiveRealToComplex _value_i26 h_88614) (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _value_i26 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i26 h_88614) (((_object_w205).val.left).val.right).wd.2.2)) (Litex.numberInC (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.2.2)) (Litex.numberInC (M := M) (1 : ℂ))))

          have h_88457 : (by
            let _equal_wd_1_0 := _object_w206
            let _equal_wd_1_1 := _object_w207
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i26)) = (M.divValue (M.addValue (Litex.denote _value_i26) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i26))) (M.number (2 : ℂ))) from h_88456) (show (M.number (1 : ℂ)) = (M.number (1 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          let _object_w208 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.sub _value_i26 (Litex.number (M := M) (1 : ℂ)) (Litex.positiveRealToComplex _value_i26 h_88614) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (Litex.subInR _value_i26 (Litex.number (M := M) (1 : ℂ)) (Litex.inRPos_real _value_i26 h_88614) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.subInC _value_i26 _wd_2_1 (Litex.positiveRealToComplex _value_i26 h_88614) (Litex.numberInC (M := M) (1 : ℂ)))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (Litex.numberInC (M := M) (1 : ℂ))));
          let _wd_1_1 := _object_w203;
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (by
              let _litex_power := (_atomic_wd_1_0).val.left
              have _elaborated_power_base := (Litex.subInC _value_i26 (Litex.number (M := M) (1 : ℂ)) (Litex.positiveRealToComplex _value_i26 h_88614) (Litex.numberInC (M := M) (1 : ℂ)))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _object_w203
            exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i26 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i26 h_88614))) (by
            let _atomic_wd_1_0 := _object_w203
            exact h_88455)))

          have h_88458 : (by
            let _equal_wd_1_0 := _object_w207
            let _equal_wd_1_1 := _object_w208
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w207;
                  let _equal_wd_1_1 := _object_w208;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((((Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614)) + ((2 : ℂ) / (Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614)))) / (2 : ℂ)) - (1 : ℂ)) (((((Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614)) - (1 : ℂ)) ^ (2 : ℕ)) + (1 : ℂ)) / ((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614)))) (Litex.NativeBridge.denoteSub (_object_w207).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w207).wd.1 (_object_w207).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w205).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w205).wd.1 (_object_w205).wd.2.1 (_object_w205).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i26 ((_object_w205).val.left).val.right ((_object_w205).val.left).wd.1 ((_object_w205).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) _value_i26 (((_object_w205).val.left).val.right).wd.1 (((_object_w205).val.left).val.right).wd.2.1 (((_object_w205).val.left).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd ((_equal_wd_1_1).val.left).val.left (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_1).val.left).wd.1 ((_equal_wd_1_1).val.left).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal (((_equal_wd_1_1).val.left).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := (((_equal_wd_1_1).val.left).val.left).val.base
                    exact (Litex.subInR _value_i26 (Litex.number (M := M) (1 : ℂ)) (Litex.inRPos_real _value_i26 h_88614) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub _value_i26 (Litex.number (M := M) (1 : ℂ)) ((((_equal_wd_1_1).val.left).val.left).val.base).wd.1 ((((_equal_wd_1_1).val.left).val.left).val.base).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i26 (_object_w203).wd.1 (_object_w203).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614)))) (by
                    have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i26 (Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614)) (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_88614)) h_88617
                    have _litex_nz_1 : ((2 : ℂ) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | exact _litex_nz_1 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          have h_88459 : (by
            let _equal_wd_1_0 := _object_w206
            let _equal_wd_1_1 := _object_w208
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_88457).trans h_88458)
                )
            )
          let _object_w209 := ((_object_w208).val.left).val.left

          have h_88460 : (by
            let _atomic_wd_1_0 := _object_w209
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w209
                    exact (by
                      let _atomic_wd_2_1 := _atomic_wd_1_0
                      exact (Litex.powStructuralNonnegativeOfEven _atomic_wd_2_1 (by
                        let _atomic_wd_3_0 := (_atomic_wd_2_1).val.base
                        exact (Litex.subInR _value_i26 (Litex.number (M := M) (1 : ℂ)) (Litex.inRPos_real _value_i26 h_88614) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num))))
                )
            )
          let _object_w210 := (let _wd_1_0 := _object_w209;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w209
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.subInC _value_i26 _wd_1_1 (Litex.positiveRealToComplex _value_i26 h_88614) (Litex.numberInC (M := M) (1 : ℂ)))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (Litex.numberInC (M := M) (1 : ℂ))))

          have h_88461 : (by
            let _atomic_wd_1_0 := _object_w210
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w210
                    exact (by
                      let _litex_zero_bound := _atomic_wd_1_0
                      exact Litex.addPositiveRight _litex_zero_bound.val.left _litex_zero_bound.val.right _litex_zero_bound.wd.1 _litex_zero_bound.wd.2 (by
                      let _atomic_wd_2_1 := _object_w209
                      exact h_88460) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))
                    ))
                )
            )
          have h_88462 : (by
            let _atomic_wd_1_0 := _object_w203
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w203
                    exact (by
                      let _litex_positive_result := _atomic_wd_1_0
                      exact Litex.mulPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_88615
                    ))
                )
            )
          have h_88463 : (by
            let _atomic_wd_1_0 := _object_w208
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w208
                    exact (by
                      let _litex_positive_result := _atomic_wd_1_0
                      exact Litex.divPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2.1 _litex_positive_result.wd.2.2 (by
                      let _atomic_wd_2_1 := _object_w210
                      exact h_88461) (by
                      let _atomic_wd_2_1 := _object_w203
                      exact h_88462)
                    ))
                )
            )
          have h_88464 : (by
            let _atomic_wd_1_0 := _object_w206
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w206
                    exact (Litex.ltOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w208 _atomic_wd_1_0 (show @Eq M.Value _ _ from Eq.refl _) (h_88459).symm h_88463))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w204
            exact (by
              let _atomic_wd_2_1 := _object_w204
              exact (Litex.subPositiveToLt _object_w206 (by
                let _atomic_wd_3_0 := _object_w204
                exact (Litex.inRPos_real _object_w204 (Litex.callInOutput _object_w204))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.ltOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w208 _object_w206 (show @Eq M.Value _ _ from Eq.refl _) (h_88459).symm h_88463))))
        )
      )
  )

theorem h_103643 : ∀ {_Host_i28 : Type v28} [_rep_i28 : Litex.Representation M _Host_i28] (_value_i28 : Litex.Obj (M := M) _Host_i28) (h_103648 : Litex.In _value_i28 (Litex.N (M := M))), (by
  let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i28 (h_10028 (M := M)) h_103648 True.intro)
  exact Litex.Le (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i28 _rep_i28 _value_i28 h_103648
          have h_103649 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i28 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i28 h_103648)
                )
            )
          have h_103795 : Litex.In _value_i28 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_103648
                )
            )
          have h_103796 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i28 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i28 h_103795)
                )
            )
          have h_112000 : ∀ (_raw_i29 : M.Value) (h_103810 : M.mem _raw_i29 (M.standard .integer)) (h_103811 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i29 = M.number (_s : ℂ) ∧ _r ≤ _s)), (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i29) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _raw_i29 h_103810 h_103811
                    let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_103810)
                    have h_103862 : Litex.In _value_i29 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i29 h_103810 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                              have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_103811)
                          )
                      )
                    exact Litex.integerInductionFromZero (fun (_raw_i29 : M.Value) => (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i29) = M.number (_s : ℂ) ∧ _r ≤ _s)) (by
                      let _raw_i29 : M.Value := M.number 0
                      have h_104097 : M.mem _raw_i29 (M.standard .integer) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num))
                      let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_104097)
                      have h_104097 : Litex.In _value_i29 (Litex.Z (M := M)) := h_104097
                      have h_104098 : Litex.Same _value_i29 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by rfl)
                            )
                        )
                      let _object_w219 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_10028 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)

                      have h_103645 : (by
                        let _equal_wd_1_0 := _object_w219
                        exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (let _equal_wd_1_0 := _object_w219;
                              (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (by
                                let _checked_call := _equal_wd_1_0
                                have _checked_case_guard : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
                                have _selected_beta := (h_10030 (M := M)) _checked_call.val.argument _checked_call.wd.2.1 _checked_case_guard
                                exact _selected_beta.trans (show @Eq M.Value _ _ from Eq.refl _))))
                            )
                        )
                      show (fun (_raw_i29 : M.Value) => (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i29) = M.number (_s : ℂ) ∧ _r ≤ _s)) (M.number 0)
                      exact (by
                        let _atomic_wd_1_0 := _object_w219
                        exact (Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0 (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (h_103645).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_right_value _litex_left_value) (by norm_num)))))
                    ) (by
                      intro _raw_i29 _induction_integer _induction_nonnegative _induction_hypothesis
                      have h_104390 : M.mem _raw_i29 (M.standard .integer) := _induction_integer
                      let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_104390)
                      have h_104390 : Litex.In _value_i29 (Litex.Z (M := M)) := h_104390
                      have h_104391 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i29 :=
                        (by
                          litex_checked_step =>
                            exact (
                              _induction_nonnegative
                            )
                        )
                      have h_104442 : Litex.In _value_i29 (Litex.N (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i29 h_104390 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_104391)
                            )
                        )
                      have h_103644 : Litex.Le (Litex.number (M := M) (1 : ℂ)) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro) :=
                        (by
                          litex_checked_step =>
                            exact (
                              _induction_hypothesis
                            )
                        )
                      let _object_w228 := (let _object_w224 := (Litex.add _value_i29 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i29 h_104390) (Litex.numberInC (M := M) (1 : ℂ)));
                      (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _object_w224 (h_10028 (M := M)) (by
                        let _atomic_wd_1_0 := _object_w224
                        exact (Litex.addInN _value_i29 (Litex.number (M := M) (1 : ℂ)) h_104442 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))

                      let _object_w229 := (let _wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro);
                      (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _wd_1_0 (h_7459 (M := M)) (Litex.inRPos_real _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (by
                          let _litex_return_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro)
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_0)).mp (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (by
                          let _litex_return_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro)
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))).2))

                      have h_103646 : (by
                        let _equal_wd_1_0 := _object_w228
                        let _equal_wd_1_1 := _object_w229
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                have h_111271 : Litex.In _value_i29 (Litex.N (M := M)) :=
                                  h_104442
                                exact (Eq.trans (Eq.symm (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i8 (M := M))) (congrArg₂ M.addValue (Litex.sameRefl _value_i29) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))))) (Eq.trans ((h_23532 (M := M)) _value_i29 h_111271) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i8 (M := M))) (Litex.sameRefl _value_i29)))))
                              )
                            )
                        )
                      have h_111281 : Litex.Lt (Litex.number (M := M) (1 : ℂ)) _object_w229 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                have h_111280 : (by
                                  let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro)
                                  exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (by
                                          let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro)
                                          exact (by
                                            let _litex_return_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro)
                                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))
                                      )
                                  )
                                have h_111353 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inRPos_positive (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro) h_111280)
                                      )
                                  )
                                have h_111354 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.ltToLe (Litex.number (M := M) 0) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro) h_111353)
                                      )
                                  )
                                have h_111355 : ¬ Litex.Same (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro) (Litex.number (M := M) (0 : ℂ)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro) h_111353) _litex_zero.symm)
                                      )
                                  )
                                exact ((h_88452 (M := M)) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_104442 True.intro) h_111280)
                              )
                            )
                        )

                      have h_111765 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_w229 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _object_w229 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_111281)
                            )
                        )
                      have h_103647 : (by
                        let _atomic_wd_1_0 := _object_w229
                        exact Litex.Lt (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := _object_w229
                                exact h_111281)
                            )
                        )

                      have h_111809 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_w229 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _object_w229 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_103647)
                            )
                        )
                      show (fun (_raw_i29 : M.Value) => (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i29) = M.number (_s : ℂ) ∧ _r ≤ _s)) (M.addValue _raw_i29 (M.number 1))
                      exact (by
                        let _atomic_wd_1_0 := _object_w228
                        exact (Litex.ltToLe (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0 (Litex.ltOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _object_w229 _atomic_wd_1_0 (show @Eq M.Value _ _ from Eq.refl _) (h_103646).symm h_111281)))
                    ) _value_i29 h_103810 h_103811
                  )
                )
            )
          exact (by
            let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i28 (h_10028 (M := M)) h_103795 True.intro)
            exact (by
              have h_112468 : Litex.In _value_i28 (Litex.Z (M := M)) :=
                (Litex.naturalToInteger _value_i28 h_103795)
              have h_112493 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i28 :=
                h_103796
              exact (Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0 _atomic_wd_1_0 (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i8 (M := M))) (Litex.sameRefl _value_i28)) ((fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value : Litex.Obj (M := M) _Host) => h_112000 (Litex.denote _value)) _value_i28 h_112468 h_112493))
            ))
        )
      )
  )

theorem h_112690 : ∀ {_Host_i31 : Type v31} [_rep_i31 : Litex.Representation M _Host_i31] (_value_i31 : Litex.Obj (M := M) _Host_i31) (h_112697 : Litex.In _value_i31 (Litex.N (M := M))), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
  let _wd_2_1 := (let _wd_3_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i31 (h_10028 (M := M)) h_112697 True.intro);
  let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_3_0
    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (by
      let _arithmetic := _atomic_wd_1_0
      exact Litex.powObjInC _arithmetic))));
  let _wd_1_1 := (let _object_w236 := (Litex.add _value_i31 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i31 h_112697) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w236 (h_10610 (M := M)) (by
    let _atomic_wd_1_0 := _object_w236
    exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_112697 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro));
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _arithmetic := _atomic_wd_1_0
      exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i31 (h_10610 (M := M)) h_112697 True.intro);
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i31 _rep_i31 _value_i31 h_112697
          have h_112698 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i31 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i31 h_112697)
                )
            )
          have h_114220 : Litex.In _value_i31 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_112697
                )
            )
          have h_114221 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i31 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i31 h_114220)
                )
            )
          let _object_w247 := (let _object_w240 := (Litex.add _value_i31 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i31 h_114220) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _object_w240 (h_10028 (M := M)) (by
            let _atomic_wd_1_0 := _object_w240
            exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_114220 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))

          let _object_w248 := (let _object_w241 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i31 (h_10028 (M := M)) h_114220 True.intro);
          (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _object_w241 (h_7459 (M := M)) (Litex.inRPos_real _object_w241 (by
            let _atomic_wd_1_0 := _object_w241
            exact (by
              let _litex_return_call := _object_w241
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w241)).mp (by
            let _atomic_wd_1_0 := _object_w241
            exact (by
              let _litex_return_call := _object_w241
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))).2))

          have h_112691 : (by
            let _equal_wd_1_0 := _object_w247
            let _equal_wd_1_1 := _object_w248
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_120059 : Litex.In _value_i31 (Litex.N (M := M)) :=
                      h_114220
                    exact (Eq.trans (Eq.symm (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i8 (M := M))) (congrArg₂ M.addValue (Litex.sameRefl _value_i31) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))))) (Eq.trans ((h_23532 (M := M)) _value_i31 h_120059) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i8 (M := M))) (Litex.sameRefl _value_i31)))))
                  )
                )
            )
          have h_112692 : (by
            let _chain_wd_112692_0 := (let _object_w249 := (_object_w247).val.argument;
            (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w249 (h_10610 (M := M)) (by
              let _atomic_wd_1_0 := _object_w249
              exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_114220 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
            let _chain_wd_112692_1 := (let _wd_1_0 := (let _wd_2_0 := _object_w247;
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_96 (M := M)) (by
              let _atomic_wd_1_0 := _object_w247
              exact (Litex.inRPos_real _object_w247 (Litex.callInOutput _object_w247))) True.intro));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
            let _chain_wd_112692_2 := _chain_wd_112692_1
            let _chain_wd_112692_3 := (let _wd_1_0 := (let _wd_2_0 := _object_w248;
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_96 (M := M)) (by
              let _atomic_wd_1_0 := _object_w248
              exact (Litex.inRPos_real _object_w248 (Litex.callInOutput _object_w248))) True.intro));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
            exact ((by
              let _equal_wd_1_0 := _chain_wd_112692_0
              let _equal_wd_1_1 := _chain_wd_112692_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_112692_2
              let _equal_wd_1_1 := _chain_wd_112692_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_112692_0 := (let _object_w249 := (_object_w247).val.argument;
                    (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w249 (h_10610 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w249
                      exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_114220 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                    let _chain_wd_112692_1 := (let _wd_1_0 := (let _wd_2_0 := _object_w247;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_96 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w247
                      exact (Litex.inRPos_real _object_w247 (Litex.callInOutput _object_w247))) True.intro));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_return_call := _atomic_wd_1_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
                    let _chain_wd_112692_2 := _chain_wd_112692_1
                    let _chain_wd_112692_3 := (let _wd_1_0 := (let _wd_2_0 := _object_w248;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_96 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w248
                      exact (Litex.inRPos_real _object_w248 (Litex.callInOutput _object_w248))) True.intro));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_return_call := _atomic_wd_1_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
                    exact (And.intro (let _equal_wd_1_0 := _chain_wd_112692_0;
                    let _equal_wd_1_1 := _chain_wd_112692_1;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))))) from by
                      have _litex_residual : (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))))) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))))) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
                      let _object_w253 := (_equal_wd_1_0).val.argument;
                      (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _wd_1_0 _object_w253 (Litex.formulaFnInFnSet _wd_1_0) (by
                        let _atomic_wd_1_0 := _object_w253
                        exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_114220 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_10611 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (Litex.denote _litex_literal.val.argument) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))))) from rfl))
                    ))).trans _litex_residual))) (congrArg (Litex.absValue (M := M)) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ))))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)))) from (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_112691)))))
                )
            )

          have h_123388 :=
            (And.left h_112692)

          have h_123389 :=
            (And.right h_112692)

          have h_123390 :=
            h_123388

          have h_123391 :=
            h_123389

          have h_123392 :=
            (Eq.trans h_123388 h_123389)
          let _object_w262 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i31 (h_10610 (M := M)) h_114220 True.intro)

          let _object_w263 := (let _wd_1_0 := (let _object_w256 := (_object_w248).val.argument;
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w256 (h_96 (M := M)) (by
            let _atomic_wd_1_0 := _object_w256
            exact (Litex.inRPos_real _object_w256 (Litex.callInOutput _object_w256))) True.intro));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))

          have h_112693 : (by
            let _equal_wd_1_0 := _object_w262
            let _equal_wd_1_1 := _object_w263
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w262;
                  let _equal_wd_1_1 := _object_w263;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i31)) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)))) from by
                    have _litex_residual : (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i31)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i31)) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
                    let _wd_1_1 := _value_i31;
                    (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_114220 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_10611 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (Litex.denote _litex_literal.val.argument) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w264 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_2_1 := (let _wd_3_0 := ((_object_w263).val.arg).val.argument;
          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (by
              let _arithmetic := _atomic_wd_1_0
              exact Litex.powObjInC _arithmetic))));
          let _wd_1_1 := (let _object_w249 := (_object_w247).val.argument;
          (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w249 (h_10610 (M := M)) (by
            let _atomic_wd_1_0 := _object_w249
            exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_114220 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro));
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _arithmetic := _atomic_wd_1_0
              exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.realToComplex (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (_object_w247).val.argument (h_10610 (M := M)) (by
              let _atomic_wd_1_0 := (_object_w247).val.argument
              exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_114220 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro) (Litex.callInOutput (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (_object_w247).val.argument (h_10610 (M := M)) (by
              let _atomic_wd_1_0 := (_object_w247).val.argument
              exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_114220 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))))))

          let _object_w265 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_2_1 := (let _wd_3_0 := ((_object_w263).val.arg).val.argument;
          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (by
              let _arithmetic := _atomic_wd_1_0
              exact Litex.powObjInC _arithmetic))));
          let _wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := _object_w248;
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_96 (M := M)) (by
            let _atomic_wd_1_0 := _object_w248
            exact (Litex.inRPos_real _object_w248 (Litex.callInOutput _object_w248))) True.intro));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _arithmetic := _atomic_wd_1_0
              exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (M.real_subset_complex _ (by
              let _litex_abs := _atomic_wd_1_0
              exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
            )))))

          have h_112694 : (by
            let _equal_wd_1_0 := _object_w264
            let _equal_wd_1_1 := _object_w265
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ M.mulValue (show (M.mulValue (M.number (4 : ℂ)) (M.powValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)) (M.number (2 : ℂ)))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)) (M.number (2 : ℂ)))) from (show @Eq M.Value _ _ from Eq.refl _)) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31))))) from h_123392))
                )
            )
          let _object_w266 := (let _wd_1_0 := _object_w262;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _object_w262
            exact (by
              let _litex_return_call := _object_w262
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

          let _object_w267 := (let _wd_1_0 := _object_w263;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _object_w263
            exact (by
              let _litex_abs := _atomic_wd_1_0
              exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
            )) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

          have h_112695 : (by
            let _equal_wd_1_0 := _object_w266
            let _equal_wd_1_1 := _object_w267
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ M.powValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i31)) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)))) from h_112693) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          have h_144208 : Litex.Same _object_w265 _object_w267 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_144207 : (by
                      let _atomic_wd_1_0 := (((_object_w264).val.left).val.right).val.base
                      exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := (((_object_w264).val.left).val.right).val.base
                              exact (by
                                let _litex_return_call := _atomic_wd_1_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))
                          )
                      )
                    have h_144269 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (((_object_w264).val.left).val.right).val.base :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive (((_object_w264).val.left).val.right).val.base h_144207)
                          )
                      )
                    have h_144270 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (((_object_w264).val.left).val.right).val.base :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) (((_object_w264).val.left).val.right).val.base h_144269)
                          )
                      )
                    have h_144271 : ¬ Litex.Same (((_object_w264).val.left).val.right).val.base (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (((_object_w264).val.left).val.right).val.base h_144269) _litex_zero.symm)
                          )
                      )
                    exact ((h_70186 (M := M)) (((_object_w264).val.left).val.right).val.base h_144207)
                  )
                )
            )
          have h_112696 : (by
            let _equal_wd_1_0 := _object_w265
            let _equal_wd_1_1 := _object_w267
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_144208
                )
            )
          exact ((((h_112694).trans h_144208)).trans (h_112695).symm)
        )
      )
  )

theorem h_147900 : ∀ {_Host_i33 : Type v33} [_rep_i33 : Litex.Representation M _Host_i33] (_value_i33 : Litex.Obj (M := M) _Host_i33) (h_147926 : Litex.In _value_i33 (Litex.N (M := M))), (by
  let _atomic_wd_1_0 := (let _object_w279 := (Litex.add _value_i33 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i33 h_147926) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w279 (h_10610 (M := M)) (by
    let _atomic_wd_2_0 := _object_w279
    exact (Litex.addInN _value_i33 (Litex.number (M := M) (1 : ℂ)) h_147926 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
  let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i33 (h_10610 (M := M)) h_147926 True.intro);
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (by
      let _litex_return_call := _atomic_wd_2_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_2_0 := _wd_1_0
    exact (by
      let _arithmetic := _atomic_wd_2_0
      exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
  exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i33 _rep_i33 _value_i33 h_147926
          have h_147927 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i33 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i33 h_147926)
                )
            )
          have h_149700 : Litex.In _value_i33 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_147926
                )
            )
          have h_149701 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i33 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i33 h_149700)
                )
            )
          have h_149703 : Litex.Le (Litex.number (M := M) (1 : ℂ)) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_149702 : Litex.In _value_i33 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_149700
                          )
                      )
                    have h_149708 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i33 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i33 h_149702)
                          )
                      )
                    exact ((h_103643 (M := M)) _value_i33 h_149702)
                  )
                )
            )
          have h_147901 : (by
            let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)
            exact Litex.Le (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)
                    exact h_149703)
                )
            )
          let _object_w285 := (let _wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro);
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.positiveRealToComplex (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.numberInC (M := M) (1 : ℂ))))

          have h_147902 : (by
            let _atomic_wd_1_0 := _object_w285
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w285
                    exact (by
                      let _litex_real_result := _atomic_wd_1_0
                      exact Litex.subInR _litex_real_result.val.left _litex_real_result.val.right (by
                      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                      exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                    ))
                )
            )
          let _object_w287 := (let _wd_1_0 := (_object_w285).val.left;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.positiveRealToComplex (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.numberInC (M := M) (1 : ℂ))))

          have h_147903 : (by
            let _atomic_wd_1_0 := _object_w287
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w287
                    exact (by
                      let _litex_real_result := _atomic_wd_1_0
                      exact Litex.addInR _litex_real_result.val.left _litex_real_result.val.right (by
                      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                      exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                    ))
                )
            )
          have h_147904 : (by
            let _atomic_wd_1_0 := _object_w285
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w285
                    exact (Litex.subNonnegative _atomic_wd_1_0 h_149703))
                )
            )
          have h_147905 : (by
            let _atomic_wd_1_0 := _object_w287
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w287
                    exact (by
                      let _litex_positive_result := _atomic_wd_1_0
                      exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 (by
                      let _atomic_wd_2_0 := (_object_w287).val.left
                      exact (Litex.inRPos_positive _atomic_wd_2_0 (by
                        let _atomic_wd_3_0 := _atomic_wd_2_0
                        exact (by
                          let _litex_return_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call))))) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
                    ))
                )
            )
          have h_147906 : (by
            let _atomic_wd_1_0 := _object_w287
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w287
                    exact (Litex.ltToLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0 h_147905))
                )
            )
          let _object_w288 := (let _wd_1_0 := _object_w285;
          let _wd_1_1 := _object_w287;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w285
            exact (M.real_subset_complex _ h_147902)) (by
            let _atomic_wd_1_0 := _object_w287
            exact (M.real_subset_complex _ h_147903))))

          have h_147907 : (by
            let _atomic_wd_1_0 := _object_w288
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w288
                    exact (by
                      let _litex_zero_bound := _atomic_wd_1_0
                      exact Litex.mulNonnegative _litex_zero_bound.val.left _litex_zero_bound.val.right _litex_zero_bound.wd.1 _litex_zero_bound.wd.2 (by
                      let _atomic_wd_2_1 := _object_w285
                      exact h_147904) (by
                      let _atomic_wd_2_1 := _object_w287
                      exact h_147906)
                    ))
                )
            )
          have h_147908 : (by
            let _chain_wd_147908_0 := (let _wd_1_0 := (let _wd_2_0 := (_object_w287).val.left;
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_2_0
              exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.sub _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _arithmetic := _atomic_wd_1_0
                exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (1 : ℂ))))
            let _chain_wd_147908_1 := _object_w288
            exact ((by
              let _equal_wd_1_0 := _chain_wd_147908_0
              let _equal_wd_1_1 := _chain_wd_147908_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _atomic_wd_1_0 := _object_w288
              exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_147908_0 := (let _wd_1_0 := (let _wd_2_0 := (_object_w287).val.left;
                    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.sub _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (1 : ℂ))))
                    let _chain_wd_147908_1 := _object_w288
                    exact (And.intro (let _equal_wd_1_0 := _chain_wd_147908_0;
                    let _equal_wd_1_1 := _chain_wd_147908_1;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro);
                    let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                    Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) ^ (2 : ℕ)) - (1 : ℂ)) (((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro);
                    let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                    Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) - (1 : ℂ)) * ((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro);
                    let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                    Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (1 : ℂ))) (Litex.NativeBridge.denoteSub (_equal_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                      let _atomic_wd_1_0 := ((_equal_wd_1_0).val.left).val.base
                      exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro);
                    let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                    Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul _object_w285 _object_w287 (by
                      let _atomic_wd_1_0 := _object_w285
                      exact (M.real_subset_complex _ h_147902)) (by
                      let _atomic_wd_1_0 := _object_w287
                      exact (M.real_subset_complex _ h_147903)) _ _ (Litex.NativeBridge.denoteSub (_object_w285).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w285).wd.1 (_object_w285).wd.2 _ _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro);
                    let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                    Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteAdd (_object_w287).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w287).wd.1 (_object_w287).wd.2 _ _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro);
                    let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                    Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (by ring!)))) (by
                      let _atomic_wd_1_0 := _object_w288
                      exact h_147907)))
                )
            )

          have h_152761 :=
            (And.left h_147908)

          have h_152762 :=
            (And.right h_147908)

          have h_152763 :=
            h_152761

          have h_152764 :=
            h_152762

          have h_152891 :=
            (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w288 (let _wd_1_0 := (let _wd_2_0 := (_object_w287).val.left;
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_2_0
              exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.sub _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _arithmetic := _atomic_wd_1_0
                exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (Eq.symm h_152761) h_152762)
          have h_147909 : (by
            let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (_object_w287).val.left;
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_2_0
              exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.sub _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _arithmetic := _atomic_wd_1_0
                exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (1 : ℂ))))
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (_object_w287).val.left;
                    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.sub _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (1 : ℂ))))
                    exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w288 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_152761).symm h_147907))
                )
            )
          let _object_w290 := (let _wd_1_0 := (_object_w287).val.left;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

          have h_147910 : (by
            let _atomic_wd_1_1 := _object_w290
            exact Litex.Le (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w290
                    exact (Litex.subNonnegativeToLe (let _wd_1_0 := (let _wd_2_0 := (_object_w287).val.left;
                    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.sub _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.powStructuralInR _atomic_wd_2_0 (by
                        let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
                        exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_147909))
                )
            )
          have h_147911 : (by
            let _atomic_wd_1_0 := _object_w290
            exact Litex.Le (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w290
                    exact h_147910)
                )
            )
          let _object_w308 := (let _object_w291 := (Litex.add _value_i33 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i33 h_149700) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w291 (h_10610 (M := M)) (by
            let _atomic_wd_1_0 := _object_w291
            exact (Litex.addInN _value_i33 (Litex.number (M := M) (1 : ℂ)) h_149700 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))

          let _object_w309 := (let _wd_1_0 := (let _object_w293 := (let _object_w292 := (Litex.add _value_i33 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i33 h_149700) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _object_w292 (h_10028 (M := M)) (by
            let _atomic_wd_1_0 := _object_w292
            exact (Litex.addInN _value_i33 (Litex.number (M := M) (1 : ℂ)) h_149700 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w293 (h_96 (M := M)) (by
            let _atomic_wd_1_0 := _object_w293
            exact (Litex.inRPos_real _object_w293 (Litex.callInOutput _object_w293))) True.intro));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))

          have h_147912 : (by
            let _equal_wd_1_0 := _object_w308
            let _equal_wd_1_1 := _object_w309
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w308;
                  let _equal_wd_1_1 := _object_w309;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))))) from by
                    have _litex_residual : (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
                    let _object_w299 := (((_equal_wd_1_1).val.arg).val.argument).val.argument;
                    (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _wd_1_0 _object_w299 (Litex.formulaFnInFnSet _wd_1_0) (by
                      let _atomic_wd_1_0 := _object_w299
                      exact (Litex.addInN _value_i33 (Litex.number (M := M) (1 : ℂ)) h_149700 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_10611 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (Litex.denote _litex_literal.val.argument) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          have h_147913 : (by
            let _atomic_wd_1_0 := _object_w309
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w309
                    exact (by
                      let _atomic_wd_2_1 := _object_w309
                      exact (by
                        let _litex_abs := _atomic_wd_2_1
                        exact Litex.absNonnegative _litex_abs.val.arg _litex_abs.wd
                      )))
                )
            )
          have h_147914 : (by
            let _atomic_wd_1_0 := _object_w308
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w308
                    exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w309 _atomic_wd_1_0 (show @Eq M.Value _ _ from Eq.refl _) (h_147912).symm h_147913))
                )
            )
          have h_147915 : (by
            let _atomic_wd_1_0 := _object_w308
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w308
                    exact (by
                      let _litex_return_call := _object_w308
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
                )
            )
          have h_147916 : (by
            let _atomic_wd_1_0 := _object_w290
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w290
                    exact (Litex.powStructuralInR _atomic_wd_1_0 (by
                      let _atomic_wd_2_0 := (_object_w290).val.base
                      exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro))))))
                )
            )
          have h_147917 : (by
            let _atomic_wd_1_1 := _object_w308
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w308
                    exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w309 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_147912).symm h_147913))
                )
            )
          let _object_w310 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := _object_w308;
          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
            let _atomic_wd_1_0 := _object_w308
            exact (M.real_subset_complex _ h_147915))))

          let _object_w311 := (let _wd_1_0 := _object_w290;
          let _wd_1_1 := _object_w308;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w290
            exact (M.real_subset_complex _ h_147916)) (by
            let _atomic_wd_1_0 := _object_w308
            exact (M.real_subset_complex _ h_147915))))

          have h_147918 : (by
            let _atomic_wd_1_0 := _object_w310
            let _atomic_wd_1_1 := _object_w311
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w310
                    let _atomic_wd_1_1 := _object_w311
                    exact (by
                      let _litex_monotone_left := _atomic_wd_1_0
                      let _litex_monotone_right := _atomic_wd_1_1
                      exact Litex.mulStructuralLeRight _litex_monotone_left _litex_monotone_right (by
                      let _atomic_wd_2_1 := _object_w308
                      exact h_147917) (by
                      let _atomic_wd_2_1 := _object_w290
                      exact h_147910) (Litex.sameRefl _litex_monotone_left.val.right)
                    ))
                )
            )
          have h_147919 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))
                )
            )

          have h_168077 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_147919)
                )
            )
          let _object_w313 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_1_1 := _object_w310;
          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _object_w310
            exact (Litex.mulInC (Litex.number (M := M) (1 : ℂ)) (_object_w310).val.right (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_147915)))))

          let _object_w314 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_1_1 := _object_w311;
          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _object_w311
            exact (Litex.mulInC (_object_w311).val.left (_object_w310).val.right (M.real_subset_complex _ h_147916) (M.real_subset_complex _ h_147915)))))

          have h_147920 : (by
            let _atomic_wd_1_0 := _object_w313
            let _atomic_wd_1_1 := _object_w314
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w313
                    let _atomic_wd_1_1 := _object_w314
                    exact (by
                      let _litex_monotone_left := _atomic_wd_1_0
                      let _litex_monotone_right := _atomic_wd_1_1
                      exact Litex.mulStructuralLeLeft _litex_monotone_left _litex_monotone_right h_147919 (by
                      let _atomic_wd_2_0 := _object_w310
                      let _atomic_wd_2_1 := _object_w311
                      exact h_147918) (Litex.sameRefl _litex_monotone_left.val.left)
                    ))
                )
            )
          let _object_w315 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_1_1 := _object_w308;
          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _object_w308
            exact (M.real_subset_complex _ h_147915))))

          have h_147921 : (by
            let _equal_wd_1_0 := _object_w313
            let _equal_wd_1_1 := _object_w315
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w313;
                  let _equal_wd_1_1 := _object_w315;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((4 : ℂ) * ((1 : ℂ) * (let _litex_numeric_call := _object_w308;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member))) ((4 : ℂ) * (let _litex_numeric_call := _object_w308;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) _object_w310 (Litex.numberInC (M := M) (4 : ℂ)) (by
                    let _atomic_wd_1_0 := _object_w310
                    exact (Litex.mulInC (Litex.number (M := M) (1 : ℂ)) (_object_w310).val.right (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_147915))) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) _object_w308 (Litex.numberInC (M := M) (1 : ℂ)) (by
                    let _atomic_wd_1_0 := _object_w308
                    exact (M.real_subset_complex _ h_147915)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (let _litex_numeric_call := _object_w308;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (let _litex_numeric_call := _object_w308;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (by ring!))))
                )
            )

          have h_172776 : Litex.Same (_object_w313).val.right (_object_w315).val.right :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.mulCancelLeftLeft (_object_w313).val.right (_object_w315).val.right (Litex.number (M := M) (4 : ℂ)) (by
                    let _atomic_wd_1_0 := _object_w310
                    exact (Litex.mulInC (Litex.number (M := M) (1 : ℂ)) (_object_w315).val.right (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_147915))) (by
                    let _atomic_wd_1_0 := _object_w308
                    exact (M.real_subset_complex _ h_147915)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_147921)
                )
            )
          let _object_w316 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_2_1 := _object_w290;
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _object_w290
            exact (M.real_subset_complex _ h_147916))));
          let _wd_1_1 := _object_w308;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (M.real_subset_complex _ h_147916))) (by
            let _atomic_wd_1_0 := _object_w308
            exact (M.real_subset_complex _ h_147915))))

          have h_147922 : (by
            let _equal_wd_1_0 := _object_w314
            let _equal_wd_1_1 := _object_w316
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w314;
                  let _equal_wd_1_1 := _object_w316;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((4 : ℂ) * (((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro);
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) ^ (2 : ℕ)) * (let _litex_numeric_call := _object_w308;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member))) (((4 : ℂ) * ((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro);
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) ^ (2 : ℕ))) * (let _litex_numeric_call := _object_w308;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) _object_w311 (Litex.numberInC (M := M) (4 : ℂ)) (by
                    let _atomic_wd_1_0 := _object_w311
                    exact (Litex.mulInC (_object_w311).val.left (_object_w310).val.right (M.real_subset_complex _ h_147916) (M.real_subset_complex _ h_147915))) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteMul _object_w290 _object_w308 (by
                    let _atomic_wd_1_0 := _object_w290
                    exact (M.real_subset_complex _ h_147916)) (by
                    let _atomic_wd_1_0 := _object_w308
                    exact (M.real_subset_complex _ h_147915)) _ _ (Litex.NativeBridge.denotePowNatReal (_object_w290).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := (_object_w290).val.base
                    exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro);
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (let _litex_numeric_call := _object_w308;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member))) (Litex.NativeBridge.denoteMul (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) ((_equal_wd_1_1).val.left).val.right ((_equal_wd_1_1).val.left).wd.1 ((_equal_wd_1_1).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denotePowNatReal (_object_w290).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := (_object_w290).val.base
                    exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_149700 True.intro);
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member))) (let _litex_numeric_call := _object_w308;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (by ring!))))
                )
            )
          have h_147923 : (by
            let _atomic_wd_1_0 := _object_w315
            let _atomic_wd_1_1 := _object_w316
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w315
                    let _atomic_wd_1_1 := _object_w316
                    exact (Litex.leOfSame _object_w313 _atomic_wd_1_0 _object_w314 _atomic_wd_1_1 h_147921 h_147922 h_147920))
                )
            )
          have h_173332 : Litex.Same _object_w316 (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i33 (h_10610 (M := M)) h_149700 True.intro);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_173331 : Litex.In _value_i33 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_149700
                          )
                      )
                    have h_173337 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i33 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i33 h_173331)
                          )
                      )
                    exact ((h_112690 (M := M)) _value_i33 h_173331)
                  )
                )
            )
          have h_147924 : (by
            let _equal_wd_1_0 := _object_w316
            let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i33 (h_10610 (M := M)) h_149700 True.intro);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_173332
                )
            )
          have h_147925 : (by
            let _atomic_wd_1_0 := _object_w315
            let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i33 (h_10610 (M := M)) h_149700 True.intro);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w315
                    let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i33 (h_10610 (M := M)) h_149700 True.intro);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_return_call := _atomic_wd_1_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    exact (Litex.leOfSame _object_w313 _atomic_wd_1_0 _object_w314 _atomic_wd_1_1 h_147921 ((h_147922).trans h_173332) h_147920))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w308
            let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i33 (h_10610 (M := M)) h_149700 True.intro);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
            let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (by
                let _arithmetic := _atomic_wd_2_0
                exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
            exact (by
              let _litex_bound_quotient := _atomic_wd_1_1
              let _litex_bound_product := _object_w315
              exact Litex.leDivOfProductBound _atomic_wd_1_0 _litex_bound_quotient _litex_bound_product (by
              let _atomic_wd_2_0 := _object_w308
              exact h_147915) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (by
              let _atomic_wd_2_0 := _object_w315
              let _atomic_wd_2_1 := (_atomic_wd_1_1).val.left
              exact (Litex.leOfSame _object_w313 _atomic_wd_2_0 _object_w314 _atomic_wd_2_1 h_147921 ((h_147922).trans h_173332) h_147920)) (Litex.sameRefl _litex_bound_product.val.left) (Litex.sameRefl _litex_bound_product.val.right)
            ))
        )
      )
  )

theorem h_188148 : ∀ {_Host_i35 : Type v35} [_rep_i35 : Litex.Representation M _Host_i35] (_value_i35 : Litex.Obj (M := M) _Host_i35) (h_188156 : Litex.In _value_i35 (Litex.N (M := M))), (by
  let _equal_wd_1_0 := (let _object_w324 := (Litex.add _value_i35 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i35 h_188156) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w324 (h_20132 (M := M)) (by
    let _atomic_wd_1_0 := _object_w324
    exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188156 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
  let _equal_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_188156 True.intro);
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _arithmetic := _atomic_wd_1_0
      exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i35 _rep_i35 _value_i35 h_188156
          have h_188157 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i35 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i35 h_188156)
                )
            )
          have h_188693 : Litex.In _value_i35 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_188156
                )
            )
          have h_188694 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i35 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i35 h_188693)
                )
            )
          let _object_i36 := (let _wd_1_0 := (_object_w77 (M := M));
          let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) _value_i35 (Litex.NativeBridge.asNat _value_i35 h_188693) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_188693 (Litex.NativeBridge.asNat_spec _value_i35 h_188693));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := h_188693
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            ))) (by
            let _atomic_wd_1_0 := (_object_w77 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := h_188693
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := h_188693
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            )))))
          have h_189580 : Litex.In _object_i36 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _wd_1_0 := (_object_w77 (M := M));
                    let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) _value_i35 (Litex.NativeBridge.asNat _value_i35 h_188693) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_188693 (Litex.NativeBridge.asNat_spec _value_i35 h_188693));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                      let _atomic_wd_2_0 := _wd_1_1
                      exact (by
                        let _litex_power := _atomic_wd_2_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ))) (by
                      let _atomic_wd_2_0 := (_object_w77 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                      let _atomic_wd_2_0 := _wd_1_1
                      exact (by
                        let _litex_power := _atomic_wd_2_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                      let _atomic_wd_2_0 := _wd_1_1
                      exact (by
                        let _litex_power := _atomic_wd_2_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      )))))
                    exact (Litex.inRPos_intro _atomic_wd_1_0 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (by
                        let _litex_power := _atomic_wd_2_0
                        have _elaborated_power_base := (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_2_0).val.base ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))
                        have _elaborated_power_exponent := (by
                        let _litex_power := (_atomic_wd_2_0).val.exponent
                        have _elaborated_power_base := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.Z (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInZ _litex_power _recorded_power_base _recorded_power_exponent
                      )
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInR _litex_power _recorded_power_base
                      )) (by
                      let _atomic_wd_2_1 := _atomic_wd_1_0
                      exact (Litex.powStructuralPositiveOfPositive _atomic_wd_2_1 (by
                        let _atomic_wd_3_1 := (_object_w77 (M := M))
                        exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_3_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                          let _atomic_wd_4_0 := (_object_w77 (M := M))
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).mpr (by
                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_3_1 (by
                          let _atomic_wd_4_0 := (_object_w77 (M := M))
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (4 : ℝ)) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_3_1 (by
                          let _atomic_wd_4_0 := (_object_w77 (M := M))
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))))
                )
            )
          have h_189581 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_i36 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _object_i36 h_189580)
                )
            )
          have h_189582 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_i36 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _object_i36 h_189581)
                )
            )
          have h_189583 : ¬ Litex.Same _object_i36 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _object_i36 h_189581) _litex_zero.symm)
                )
            )
          have h_189584 : Litex.Same _object_i36 _object_i36 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.sameRefl (let _wd_1_0 := (_object_w77 (M := M));
                  let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) _value_i35 (Litex.NativeBridge.asNat _value_i35 h_188693) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_188693 (Litex.NativeBridge.asNat_spec _value_i35 h_188693));
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ))) (by
                    let _atomic_wd_1_0 := (_object_w77 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ))))))
                )
            )
          have h_188149 : (by
            let _chain_wd_188149_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_188693 True.intro)
            let _chain_wd_188149_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
            let _wd_1_1 := _object_i36;
            (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := _object_i36
              exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580)))))
            let _chain_wd_188149_2 := _chain_wd_188149_1
            let _chain_wd_188149_3 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_189580))
            exact ((by
              let _equal_wd_1_0 := _chain_wd_188149_0
              let _equal_wd_1_1 := _chain_wd_188149_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_188149_2
              let _equal_wd_1_1 := _chain_wd_188149_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_188149_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_188693 True.intro)
                    let _chain_wd_188149_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
                    let _wd_1_1 := _object_i36;
                    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                      let _atomic_wd_1_0 := _object_i36
                      exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580)))))
                    let _chain_wd_188149_2 := _chain_wd_188149_1
                    let _chain_wd_188149_3 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_189580))
                    exact (And.intro (let _equal_wd_1_0 := _chain_wd_188149_0;
                    let _equal_wd_1_1 := _chain_wd_188149_1;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (Litex.denote _value_i35)) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35)))) from by
                      have _litex_residual : (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35)))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35)))) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (Litex.denote _value_i35)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (Litex.denote _value_i35)) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35)))) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_1_0 := (_object_i15 (M := M));
                      let _wd_1_1 := _value_i35;
                      (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_188693 True.intro))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_20133 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35)))) from rfl))
                    ))).trans _litex_residual))) (congrArg₂ M.mulValue (show (M.number (4 : ℂ)) = (M.number (4 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)) (show (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35))) = (Litex.denote _object_i36) from (h_189584).symm))))
                )
            )

          have h_190501 :=
            (And.left h_188149)

          have h_190502 :=
            (And.right h_188149)

          have h_190503 :=
            h_190501

          have h_190504 :=
            h_190502

          have h_190505 :=
            (Eq.trans h_190501 h_190502)
          let _object_w332 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (Litex.add _value_i35 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i35 h_188693) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))))) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))))))

          let _object_w333 := (let _wd_1_0 := (_object_i36).val.exponent;
          let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)));
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.numberInC (M := M) (2 : ℂ))
              have _elaborated_power_exponent := (Litex.naturalToInteger _value_i35 h_188693)
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) ^ (1 : ℕ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ))))))

          have h_188150 : (by
            let _equal_wd_1_0 := _object_w332
            let _equal_wd_1_1 := _object_w333
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w332;
                  let _equal_wd_1_1 := _object_w333;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Eq.symm (by
                    have _litex_base_complex : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.C (M := M)) := (Litex.numberInC (M := M) (2 : ℂ))
                    have _litex_first_natural : Litex.In _value_i35 (Litex.N (M := M)) := h_188693
                    have _litex_second_natural : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.N (M := M)) := (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))
                    let _litex_base_value : ℂ := Litex.NativeBridge.asComplex (Litex.number (M := M) (2 : ℂ)) _litex_base_complex
                    have _litex_base_denote : Litex.denote (Litex.number (M := M) (2 : ℂ)) = M.number _litex_base_value := Litex.NativeBridge.asComplex_spec (Litex.number (M := M) (2 : ℂ)) _litex_base_complex
                    let _litex_n1 : ℕ := Litex.NativeBridge.asNat _value_i35 _litex_first_natural
                    let _litex_n2 : ℕ := Litex.NativeBridge.asNat (Litex.number (M := M) (1 : ℂ)) _litex_second_natural
                    have _litex_exp1 : Litex.Same _value_i35 (Litex.number (M := M) (_litex_n1 : ℂ)) := Litex.NativeBridge.asNat_spec _value_i35 _litex_first_natural
                    have _litex_exp2 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (_litex_n2 : ℂ)) := Litex.NativeBridge.asNat_spec (Litex.number (M := M) (1 : ℂ)) _litex_second_natural
                    let _litex_product := _equal_wd_1_1
                    let _litex_combined := _equal_wd_1_0
                    have _litex_combined_exponent : Litex.Same _litex_combined.val.exponent (Litex.number (M := M) (((_litex_n1 + _litex_n2 : ℕ) : ℂ))) := (by
                      let _litex_exponent := (_equal_wd_1_0).val.exponent
                      change M.addValue (Litex.denote _litex_exponent.val.left) (Litex.denote _litex_exponent.val.right) = M.number (((_litex_n1 + _litex_n2 : ℕ) : ℂ))
                      have _litex_first_value := _litex_exp1
                      have _litex_second_value := _litex_exp2
                      change Litex.denote _litex_exponent.val.left = M.number (_litex_n1 : ℂ) at _litex_first_value
                      change Litex.denote _litex_exponent.val.right = M.number (_litex_n2 : ℂ) at _litex_second_value
                      rw [_litex_first_value, _litex_second_value, M.add_numbers]
                      exact congrArg M.number (Nat.cast_add _litex_n1 _litex_n2).symm)
                    have _litex_factor_left : Litex.denote _litex_product.val.left = M.number (_litex_base_value ^ _litex_n1) := (Litex.NativeBridge.denotePowStructuralNat (_equal_wd_1_1).val.left _litex_n1 _litex_exp1 _litex_base_value _litex_base_denote)
                    have _litex_factor_right : Litex.denote _litex_product.val.right = M.number (_litex_base_value ^ _litex_n2) := (Litex.NativeBridge.denotePowStructuralNat (_equal_wd_1_1).val.right _litex_n2 _litex_exp2 _litex_base_value _litex_base_denote)
                    exact Litex.NativeBridge.sameOfDenoteNumber _litex_product _litex_combined ((_litex_base_value ^ _litex_n1) * (_litex_base_value ^ _litex_n2)) (_litex_base_value ^ (_litex_n1 + _litex_n2)) (Litex.NativeBridge.denoteMul _litex_product.val.left _litex_product.val.right _litex_product.wd.1 _litex_product.wd.2 _ _ _litex_factor_left _litex_factor_right) (Litex.NativeBridge.denotePowStructuralNat _litex_combined (_litex_n1 + _litex_n2) _litex_combined_exponent _litex_base_value _litex_base_denote) (pow_add _litex_base_value _litex_n1 _litex_n2).symm
                  ))))
                )
            )

          have h_191180 : Litex.In _object_w333 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_190910 : (by
                    let _atomic_wd_1_1 := _object_w332
                    exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
                    let _atomic_wd_1_1 := _object_w332
                    exact (Litex.powStructuralPositiveOfPositive _atomic_wd_1_1 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
                    have h_191058 : (by
                    let _atomic_wd_1_0 := (_object_w332).val.exponent
                    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) := (by
                    let _atomic_wd_1_0 := (_object_w332).val.exponent
                    exact (Litex.addInR _value_i35 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToReal _value_i35 h_188693) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))
                    exact Litex.inOfSame _object_w332 _object_w333 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_188150 (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro _object_w332 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_190910; exact (M.real_members (Litex.denote _object_w332)).mpr ⟨_litex_real, _litex_value⟩) h_190910)
                  )
                )
            )
          let _object_w334 := (_object_w333).val.right

          have h_188151 : (by
            let _equal_wd_1_0 := _object_w334
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w334;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) ((2 : ℂ) ^ (1 : ℕ)) (2 : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
                )
            )

          have h_191282 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_191220 : (by
                    let _atomic_wd_1_1 := _object_w334
                    exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
                    let _atomic_wd_1_1 := _object_w334
                    exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                      let _atomic_wd_2_0 := _object_w334
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (1 : ℕ)) (Litex.R (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) ^ (1 : ℕ)) (2 : ℝ) (by norm_num))))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _object_w334
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (1 : ℕ)) (Litex.R (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) ^ (1 : ℕ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _object_w334
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (1 : ℕ)) (Litex.R (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) ^ (1 : ℕ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                    have h_191263 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                    exact Litex.inOfSame _object_w334 (Litex.number (M := M) (2 : ℂ)) (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_188151 (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro _object_w334 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_191220; exact (M.real_members (Litex.denote _object_w334)).mpr ⟨_litex_real, _litex_value⟩) h_191220)
                  )
                )
            )
          let _object_w336 := (let _wd_1_0 := (_object_w333).val.left;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.numberInC (M := M) (2 : ℂ))
              have _elaborated_power_exponent := (Litex.naturalToInteger _value_i35 h_188693)
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (Litex.numberInC (M := M) (2 : ℂ))))

          have h_188152 : (by
            let _equal_wd_1_0 := _object_w332
            let _equal_wd_1_1 := _object_w336
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w332;
                  let _equal_wd_1_1 := _object_w336;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Eq.symm (by
                    have _litex_base_complex : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.C (M := M)) := (Litex.numberInC (M := M) (2 : ℂ))
                    have _litex_first_natural : Litex.In _value_i35 (Litex.N (M := M)) := h_188693
                    have _litex_second_natural : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.N (M := M)) := (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))
                    let _litex_base_value : ℂ := Litex.NativeBridge.asComplex (Litex.number (M := M) (2 : ℂ)) _litex_base_complex
                    have _litex_base_denote : Litex.denote (Litex.number (M := M) (2 : ℂ)) = M.number _litex_base_value := Litex.NativeBridge.asComplex_spec (Litex.number (M := M) (2 : ℂ)) _litex_base_complex
                    let _litex_n1 : ℕ := Litex.NativeBridge.asNat _value_i35 _litex_first_natural
                    let _litex_n2 : ℕ := Litex.NativeBridge.asNat (Litex.number (M := M) (1 : ℂ)) _litex_second_natural
                    have _litex_exp1 : Litex.Same _value_i35 (Litex.number (M := M) (_litex_n1 : ℂ)) := Litex.NativeBridge.asNat_spec _value_i35 _litex_first_natural
                    have _litex_exp2 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (_litex_n2 : ℂ)) := Litex.NativeBridge.asNat_spec (Litex.number (M := M) (1 : ℂ)) _litex_second_natural
                    let _litex_product := _equal_wd_1_1
                    let _litex_combined := _equal_wd_1_0
                    have _litex_combined_exponent : Litex.Same _litex_combined.val.exponent (Litex.number (M := M) (((_litex_n1 + _litex_n2 : ℕ) : ℂ))) := (by
                      let _litex_exponent := (_object_w332).val.exponent
                      change M.addValue (Litex.denote _litex_exponent.val.left) (Litex.denote _litex_exponent.val.right) = M.number (((_litex_n1 + _litex_n2 : ℕ) : ℂ))
                      have _litex_first_value := _litex_exp1
                      have _litex_second_value := _litex_exp2
                      change Litex.denote _litex_exponent.val.left = M.number (_litex_n1 : ℂ) at _litex_first_value
                      change Litex.denote _litex_exponent.val.right = M.number (_litex_n2 : ℂ) at _litex_second_value
                      rw [_litex_first_value, _litex_second_value, M.add_numbers]
                      exact congrArg M.number (Nat.cast_add _litex_n1 _litex_n2).symm)
                    have _litex_factor_left : Litex.denote _litex_product.val.left = M.number (_litex_base_value ^ _litex_n1) := (Litex.NativeBridge.denotePowStructuralNat (_equal_wd_1_1).val.left _litex_n1 _litex_exp1 _litex_base_value _litex_base_denote)
                    have _litex_factor_right : Litex.denote _litex_product.val.right = M.number (_litex_base_value ^ _litex_n2) := (by
                      change Litex.denote (Litex.number (M := M) (2 : ℂ)) = M.number (_litex_base_value ^ _litex_n2)
                      have _litex_one : _litex_n2 = 1 := Litex.NativeBridge.asNat_ofDenote (Litex.number (M := M) (1 : ℂ)) _litex_second_natural 1 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num))
                      simpa only [_litex_one, pow_one] using _litex_base_denote)
                    exact Litex.NativeBridge.sameOfDenoteNumber _litex_product _litex_combined ((_litex_base_value ^ _litex_n1) * (_litex_base_value ^ _litex_n2)) (_litex_base_value ^ (_litex_n1 + _litex_n2)) (Litex.NativeBridge.denoteMul _litex_product.val.left _litex_product.val.right _litex_product.wd.1 _litex_product.wd.2 _ _ _litex_factor_left _litex_factor_right) (Litex.NativeBridge.denotePowStructuralNat _litex_combined (_litex_n1 + _litex_n2) _litex_combined_exponent _litex_base_value _litex_base_denote) (pow_add _litex_base_value _litex_n1 _litex_n2).symm
                  ))))
                )
            )

          have h_191760 : Litex.In _object_w336 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_191481 : (by
                    let _atomic_wd_1_1 := _object_w332
                    exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
                    let _atomic_wd_1_1 := _object_w332
                    exact (Litex.powStructuralPositiveOfPositive _atomic_wd_1_1 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
                    have h_191612 : (by
                    let _atomic_wd_1_0 := (_object_w332).val.exponent
                    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) := (by
                    let _atomic_wd_1_0 := (_object_w332).val.exponent
                    exact (Litex.addInR _value_i35 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToReal _value_i35 h_188693) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))
                    exact Litex.inOfSame _object_w332 _object_w336 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_188152 (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro _object_w332 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_191481; exact (M.real_members (Litex.denote _object_w332)).mpr ⟨_litex_real, _litex_value⟩) h_191481)
                  )
                )
            )
          have h_188153 : (by
            let _chain_wd_188153_0 := (let _wd_1_0 := (_object_w77 (M := M));
            let _wd_1_1 := _object_w332;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w332
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := (_object_w77 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w332
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w332
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              )))))
            let _chain_wd_188153_1 := (let _wd_1_0 := (_object_w77 (M := M));
            let _wd_1_1 := _object_w336;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w336
              exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w336).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_188693
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
              let _atomic_wd_1_0 := (_object_w77 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w336
              exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w336).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_188693
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w336
              exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w336).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_188693
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))))
            let _chain_wd_188153_2 := _chain_wd_188153_1
            let _chain_wd_188153_3 := (let _wd_1_0 := _object_i36;
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_i36
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            let _chain_wd_188153_4 := _chain_wd_188153_3
            let _chain_wd_188153_5 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
            exact ((by
              let _equal_wd_1_0 := _chain_wd_188153_0
              let _equal_wd_1_1 := _chain_wd_188153_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
              let _equal_wd_1_0 := _chain_wd_188153_2
              let _equal_wd_1_1 := _chain_wd_188153_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_188153_4
              let _equal_wd_1_1 := _chain_wd_188153_5
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_188153_0 := (let _wd_1_0 := (_object_w77 (M := M));
                    let _wd_1_1 := _object_w332;
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w332
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ))) (by
                      let _atomic_wd_1_0 := (_object_w77 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                      let _atomic_wd_1_0 := _object_w332
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w332
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      )))))
                    let _chain_wd_188153_1 := (let _wd_1_0 := (_object_w77 (M := M));
                    let _wd_1_1 := _object_w336;
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                      let _atomic_wd_1_0 := (_object_w77 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))))
                    let _chain_wd_188153_2 := _chain_wd_188153_1
                    let _chain_wd_188153_3 := (let _wd_1_0 := _object_i36;
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _object_i36
                      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    let _chain_wd_188153_4 := _chain_wd_188153_3
                    let _chain_wd_188153_5 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                    exact (And.intro (congrArg₂ M.powValue (show (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) from (show @Eq M.Value _ _ from Eq.refl _)) (show (M.powValue (M.number (2 : ℂ)) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))) = (M.mulValue (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35)) (M.number (2 : ℂ))) from h_188152)) (And.intro (let _equal_wd_1_0 := _chain_wd_188153_2;
                    let _equal_wd_1_1 := _chain_wd_188153_3;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Eq.symm (by
                      have _litex_base_complex : Litex.In (_equal_wd_1_0).val.base (Litex.C (M := M)) := (by
                      let _atomic_wd_1_0 := (_object_w77 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (4 : ℂ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ)))))
                      have _litex_first_natural : Litex.In (_object_w336).val.left (Litex.N (M := M)) := (by
                      let _atomic_wd_1_0 := (_object_w336).val.left
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ))
                      have _litex_second_natural : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      let _litex_base_value : ℂ := Litex.NativeBridge.asComplex (_equal_wd_1_0).val.base _litex_base_complex
                      have _litex_base_denote : Litex.denote (_equal_wd_1_0).val.base = M.number _litex_base_value := Litex.NativeBridge.asComplex_spec (_equal_wd_1_0).val.base _litex_base_complex
                      let _litex_n1 : ℕ := Litex.NativeBridge.asNat (_object_w336).val.left _litex_first_natural
                      let _litex_n2 : ℕ := Litex.NativeBridge.asNat (Litex.number (M := M) (2 : ℂ)) _litex_second_natural
                      have _litex_exp1 : Litex.Same (_object_w336).val.left (Litex.number (M := M) (_litex_n1 : ℂ)) := Litex.NativeBridge.asNat_spec (_object_w336).val.left _litex_first_natural
                      have _litex_exp2 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (_litex_n2 : ℂ)) := Litex.NativeBridge.asNat_spec (Litex.number (M := M) (2 : ℂ)) _litex_second_natural
                      let _litex_nested := _equal_wd_1_1
                      let _litex_combined := _equal_wd_1_0
                      have _litex_combined_exponent : Litex.Same _litex_combined.val.exponent (Litex.number (M := M) (((_litex_n1 * _litex_n2 : ℕ) : ℂ))) := (by
                        let _litex_exponent := (_equal_wd_1_0).val.exponent
                        change M.mulValue (Litex.denote _litex_exponent.val.left) (Litex.denote _litex_exponent.val.right) = M.number (((_litex_n1 * _litex_n2 : ℕ) : ℂ))
                        have _litex_first_value := _litex_exp1
                        have _litex_second_value := _litex_exp2
                        change Litex.denote _litex_exponent.val.left = M.number (_litex_n1 : ℂ) at _litex_first_value
                        change Litex.denote _litex_exponent.val.right = M.number (_litex_n2 : ℂ) at _litex_second_value
                        rw [_litex_first_value, _litex_second_value, M.mul_numbers]
                        exact congrArg M.number (Nat.cast_mul _litex_n1 _litex_n2).symm)
                      have _litex_inner_denote : Litex.denote _litex_nested.val.base = M.number (_litex_base_value ^ _litex_n1) := Litex.NativeBridge.denotePowStructuralNat _litex_nested.val.base _litex_n1 _litex_exp1 _litex_base_value _litex_base_denote
                      exact Litex.NativeBridge.sameOfDenoteNumber _litex_nested _litex_combined ((_litex_base_value ^ _litex_n1) ^ _litex_n2) (_litex_base_value ^ (_litex_n1 * _litex_n2)) (Litex.NativeBridge.denotePowStructuralNat _litex_nested _litex_n2 _litex_exp2 (_litex_base_value ^ _litex_n1) _litex_inner_denote) (Litex.NativeBridge.denotePowStructuralNat _litex_combined (_litex_n1 * _litex_n2) _litex_combined_exponent _litex_base_value _litex_base_denote) (pow_mul _litex_base_value _litex_n1 _litex_n2).symm
                    )))) (congrArg₂ M.powValue (show (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35))) = (Litex.denote _object_i36) from (h_189584).symm) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _))))))
                )
            )

          have h_192562 :=
            (And.left h_188153)

          have h_192563 :=
            (And.left (And.right h_188153))

          have h_192564 :=
            (And.right (And.right h_188153))

          have h_192565 :=
            h_192562

          have h_193112 : Litex.In (let _wd_1_0 := (_object_w77 (M := M));
          let _wd_1_1 := _object_w336;
          (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w336
            exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
              let _litex_power := (_object_w336).val.left
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := h_188693
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
            let _atomic_wd_1_0 := (_object_w77 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
            let _atomic_wd_1_0 := _object_w336
            exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
              let _litex_power := (_object_w336).val.left
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := h_188693
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w336
            exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
              let _litex_power := (_object_w336).val.left
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := h_188693
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_192568 : (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := (_object_w77 (M := M));
                    let _wd_1_1 := _object_w332;
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                      let _atomic_wd_2_0 := _object_w332
                      exact (by
                        let _litex_power := _atomic_wd_2_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ))) (by
                      let _atomic_wd_2_0 := (_object_w77 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                      let _atomic_wd_2_0 := _object_w332
                      exact (by
                        let _litex_power := _atomic_wd_2_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                      let _atomic_wd_2_0 := _object_w332
                      exact (by
                        let _litex_power := _atomic_wd_2_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      )))))
                    exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := (_object_w77 (M := M));
                    let _wd_1_1 := _object_w332;
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                      let _atomic_wd_2_0 := _object_w332
                      exact (by
                        let _litex_power := _atomic_wd_2_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ))) (by
                      let _atomic_wd_2_0 := (_object_w77 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                      let _atomic_wd_2_0 := _object_w332
                      exact (by
                        let _litex_power := _atomic_wd_2_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                      let _atomic_wd_2_0 := _object_w332
                      exact (by
                        let _litex_power := _atomic_wd_2_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      )))))
                    exact (Litex.powStructuralPositiveOfPositive _atomic_wd_1_1 (by
                      let _atomic_wd_2_1 := (_object_w77 (M := M))
                      exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                        let _atomic_wd_3_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).mpr (by
                        have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                        have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_2_1 (by
                        let _atomic_wd_3_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (4 : ℝ)) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_1 (by
                        let _atomic_wd_3_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                    have h_193051 : (by
                    let _atomic_wd_1_0 := _object_w332
                    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) := (by
                    let _atomic_wd_1_0 := _object_w332
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_w333 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (h_188150).symm (show @Eq M.Value _ _ from Eq.refl _) h_191180)))
                    exact Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
                  let _wd_1_1 := _object_w332;
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w332
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ))) (by
                    let _atomic_wd_1_0 := (_object_w77 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _object_w332
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w332
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ))))) (let _wd_1_0 := (_object_w77 (M := M));
                  let _wd_1_1 := _object_w336;
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                    let _atomic_wd_1_0 := (_object_w77 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_192565 (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (let _wd_1_0 := (_object_w77 (M := M));
                  let _wd_1_1 := _object_w332;
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w332
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ))) (by
                    let _atomic_wd_1_0 := (_object_w77 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _object_w332
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w332
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ))))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_192568; exact (M.real_members (Litex.denote (let _wd_1_0 := (_object_w77 (M := M));
                  let _wd_1_1 := _object_w332;
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w332
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ))) (by
                    let _atomic_wd_1_0 := (_object_w77 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _object_w332
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w332
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ))))))).mpr ⟨_litex_real, _litex_value⟩) h_192568)
                  )
                )
            )

          have h_193327 : Litex.In (let _wd_1_0 := (_object_w77 (M := M));
          let _wd_1_1 := _object_w332;
          (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w332
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            ))) (by
            let _atomic_wd_1_0 := (_object_w77 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
            let _atomic_wd_1_0 := _object_w332
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w332
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            ))))) (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_193113 : (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := (_object_w77 (M := M));
                    let _wd_1_1 := _object_w336;
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                      let _atomic_wd_1_0 := (_object_w77 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))))
                    exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := (_object_w77 (M := M));
                    let _wd_1_1 := _object_w336;
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                      let _atomic_wd_1_0 := (_object_w77 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))))
                    exact (Litex.powStructuralPositiveOfPositive _atomic_wd_1_1 (by
                      let _atomic_wd_2_1 := (_object_w77 (M := M))
                      exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                        let _atomic_wd_3_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).mpr (by
                        have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                        have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_2_1 (by
                        let _atomic_wd_3_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (4 : ℝ)) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_1 (by
                        let _atomic_wd_3_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                    have h_193262 : (by
                    let _atomic_wd_1_0 := _object_w336
                    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) := (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_w333 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (((h_188150).symm).trans h_188152) (show @Eq M.Value _ _ from Eq.refl _) h_191180)))
                    exact Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
                  let _wd_1_1 := _object_w336;
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                    let _atomic_wd_1_0 := (_object_w77 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (let _wd_1_0 := (_object_w77 (M := M));
                  let _wd_1_1 := _object_w332;
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w332
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ))) (by
                    let _atomic_wd_1_0 := (_object_w77 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _object_w332
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w332
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ))))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Eq.symm h_192565) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (let _wd_1_0 := (_object_w77 (M := M));
                  let _wd_1_1 := _object_w336;
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                    let _atomic_wd_1_0 := (_object_w77 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_193113; exact (M.real_members (Litex.denote (let _wd_1_0 := (_object_w77 (M := M));
                  let _wd_1_1 := _object_w336;
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                    let _atomic_wd_1_0 := (_object_w77 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))))).mpr ⟨_litex_real, _litex_value⟩) h_193113)
                  )
                )
            )

          have h_192566 :=
            h_192563

          have h_193563 : Litex.In (let _wd_1_0 := _object_i36;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _object_i36
            exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_193328 : (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := (_object_w77 (M := M));
                    let _wd_1_1 := _object_w336;
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                      let _atomic_wd_1_0 := (_object_w77 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))))
                    exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := (_object_w77 (M := M));
                    let _wd_1_1 := _object_w336;
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                      let _atomic_wd_1_0 := (_object_w77 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))))
                    exact (Litex.powStructuralPositiveOfPositive _atomic_wd_1_1 (by
                      let _atomic_wd_2_1 := (_object_w77 (M := M))
                      exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                        let _atomic_wd_3_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).mpr (by
                        have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                        have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_2_1 (by
                        let _atomic_wd_3_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (4 : ℝ)) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_1 (by
                        let _atomic_wd_3_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                    have h_193494 : (by
                    let _atomic_wd_1_0 := _object_w336
                    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) := (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_w333 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (((h_188150).symm).trans h_188152) (show @Eq M.Value _ _ from Eq.refl _) h_191180)))
                    exact Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
                  let _wd_1_1 := _object_w336;
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                    let _atomic_wd_1_0 := (_object_w77 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (let _wd_1_0 := _object_i36;
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_i36
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_192566 (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (let _wd_1_0 := (_object_w77 (M := M));
                  let _wd_1_1 := _object_w336;
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                    let _atomic_wd_1_0 := (_object_w77 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_193328; exact (M.real_members (Litex.denote (let _wd_1_0 := (_object_w77 (M := M));
                  let _wd_1_1 := _object_w336;
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                    let _atomic_wd_1_0 := (_object_w77 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))))).mpr ⟨_litex_real, _litex_value⟩) h_193328)
                  )
                )
            )

          have h_193793 : Litex.In (let _wd_1_0 := (_object_w77 (M := M));
          let _wd_1_1 := _object_w336;
          (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w336
            exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
              let _litex_power := (_object_w336).val.left
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := h_188693
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
            let _atomic_wd_1_0 := (_object_w77 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
            let _atomic_wd_1_0 := _object_w336
            exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
              let _litex_power := (_object_w336).val.left
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := h_188693
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w336
            exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
              let _litex_power := (_object_w336).val.left
              have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
              have _elaborated_power_exponent := h_188693
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
            ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_193564 : (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := _object_i36;
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _object_i36
                      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := _object_i36;
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _object_i36
                      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    exact (Litex.powStructuralPositiveOfEven _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _object_i36
                      exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.inOfSame _object_i36 _atomic_wd_2_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num) (by norm_num) (by
                      let _atomic_wd_2_0 := _object_i36
                      exact (Litex.notSameOfSame _object_i36 _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189583))))
                    have h_193762 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                    exact Litex.inOfSame (let _wd_1_0 := _object_i36;
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_i36
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (let _wd_1_0 := (_object_w77 (M := M));
                  let _wd_1_1 := _object_w336;
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                    let _atomic_wd_1_0 := (_object_w77 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w336
                    exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                      let _litex_power := (_object_w336).val.left
                      have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                      have _elaborated_power_exponent := h_188693
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                    ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Eq.symm h_192566) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (let _wd_1_0 := _object_i36;
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_i36
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_193564; exact (M.real_members (Litex.denote (let _wd_1_0 := _object_i36;
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_i36
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))).mpr ⟨_litex_real, _litex_value⟩) h_193564)
                  )
                )
            )

          have h_192567 :=
            h_192564

          have h_194042 : Litex.In (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_193794 : (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := _object_i36;
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _object_i36
                      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := _object_i36;
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _object_i36
                      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    exact (Litex.powStructuralPositiveOfEven _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _object_i36
                      exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.inOfSame _object_i36 _atomic_wd_2_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num) (by norm_num) (by
                      let _atomic_wd_2_0 := _object_i36
                      exact (Litex.notSameOfSame _object_i36 _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189583))))
                    have h_194009 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                    exact Litex.inOfSame (let _wd_1_0 := _object_i36;
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_i36
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_192567 (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (let _wd_1_0 := _object_i36;
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_i36
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_193794; exact (M.real_members (Litex.denote (let _wd_1_0 := _object_i36;
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_i36
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))).mpr ⟨_litex_real, _litex_value⟩) h_193794)
                  )
                )
            )

          have h_194310 : Litex.In (let _wd_1_0 := _object_i36;
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _object_i36
            exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_194043 : (by
                    let _atomic_wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                    exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
                    let _atomic_wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                    exact (Litex.powStructuralPositiveOfEven _atomic_wd_1_1 (Litex.inRPos_real _object_i36 h_189580) (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num) (by norm_num) h_189583))
                    have h_194275 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                    exact Litex.inOfSame (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (let _wd_1_0 := _object_i36;
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _object_i36
                    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_189584 (show @Eq M.Value _ _ from Eq.refl _) h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Eq.symm h_192567) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_194043; exact (M.real_members (Litex.denote (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))).mpr ⟨_litex_real, _litex_value⟩) h_194043)
                  )
                )
            )

          have h_194311 :=
            (Eq.trans h_192562 h_192563)

          have h_194312 :=
            (Eq.trans (Eq.trans h_192562 h_192563) h_192564)

          have h_194313 :=
            (Eq.trans h_192563 h_192564)
          have h_188154 : (by
            let _chain_wd_188154_0 := (let _object_w341 := (_object_w332).val.exponent;
            (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w341 (h_20132 (M := M)) (by
              let _atomic_wd_1_0 := _object_w341
              exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
            let _chain_wd_188154_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
            let _wd_1_1 := (let _wd_1_0 := (_object_w77 (M := M));
            let _wd_1_1 := _object_w332;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w332
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := (_object_w77 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w332
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w332
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              )))));
            (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
              let _wd_1_1 := _object_w336;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                let _atomic_wd_1_0 := (_object_w77 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (h_192562).symm (show @Eq M.Value _ _ from Eq.refl _) h_193112)))))
            let _chain_wd_188154_2 := _chain_wd_188154_1
            let _chain_wd_188154_3 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
            let _wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
              let _wd_1_1 := _object_w336;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                let _atomic_wd_1_0 := (_object_w77 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_194313 (show @Eq M.Value _ _ from Eq.refl _) h_193112)))))
            exact ((by
              let _equal_wd_1_0 := _chain_wd_188154_0
              let _equal_wd_1_1 := _chain_wd_188154_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_188154_2
              let _equal_wd_1_1 := _chain_wd_188154_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_188154_0 := (let _object_w341 := (_object_w332).val.exponent;
                    (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w341 (h_20132 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w341
                      exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                    let _chain_wd_188154_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
                    let _wd_1_1 := (let _wd_1_0 := (_object_w77 (M := M));
                    let _wd_1_1 := _object_w332;
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w332
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ))) (by
                      let _atomic_wd_1_0 := (_object_w77 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                      let _atomic_wd_1_0 := _object_w332
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w332
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      )))));
                    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
                      let _wd_1_1 := _object_w336;
                      (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                        let _atomic_wd_1_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (h_192562).symm (show @Eq M.Value _ _ from Eq.refl _) h_193112)))))
                    let _chain_wd_188154_2 := _chain_wd_188154_1
                    let _chain_wd_188154_3 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
                    let _wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
                      let _wd_1_1 := _object_w336;
                      (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                        let _atomic_wd_1_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_194313 (show @Eq M.Value _ _ from Eq.refl _) h_193112)))))
                    exact (And.intro (let _equal_wd_1_0 := _chain_wd_188154_0;
                    let _equal_wd_1_1 := _chain_wd_188154_1;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))))) from by
                      have _litex_residual : (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))))) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))))) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_1_0 := (_object_i15 (M := M));
                      let _object_w349 := (_equal_wd_1_0).val.argument;
                      (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _wd_1_0 _object_w349 (Litex.formulaFnInFnSet _wd_1_0) (by
                        let _atomic_wd_1_0 := _object_w349
                        exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_188693 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_20133 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))))) from rfl))
                    ))).trans _litex_residual))) (congrArg₂ M.mulValue (show (M.number (4 : ℂ)) = (M.number (4 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)) (show (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ))))) = (M.powValue (Litex.denote _object_i36) (M.number (2 : ℂ))) from h_194312))))
                )
            )

          have h_197809 :=
            (And.left h_188154)

          have h_197810 :=
            (And.right h_188154)

          have h_197811 :=
            h_197809

          have h_197812 :=
            h_197810

          have h_197813 :=
            (Eq.trans h_197809 h_197810)
          have h_188155 : (by
            let _chain_wd_188155_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_188693 True.intro);
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_2_0
              exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_188693 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_188693 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
            let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _arithmetic := _atomic_wd_1_0
                exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
            let _chain_wd_188155_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_189580));
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_2_0
              exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (Litex.inRPos_real _object_i36 h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
            let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.mulInC _wd_1_1 _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_189580))
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              )) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
            let _chain_wd_188155_2 := _chain_wd_188155_1
            let _chain_wd_188155_3 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (16 : ℂ));
            let _wd_2_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (16 : ℂ)) (by
              let _atomic_wd_1_0 := _wd_2_1
              exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
              let _wd_1_1 := _object_w336;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                let _atomic_wd_1_0 := (_object_w77 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_194313 (show @Eq M.Value _ _ from Eq.refl _) h_193112)))));
            let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.mulInC (Litex.number (M := M) (16 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (16 : ℂ)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
              let _wd_1_1 := _object_w336;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                let _atomic_wd_1_0 := (_object_w77 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (_atomic_wd_1_0).val.right (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_194313 (show @Eq M.Value _ _ from Eq.refl _) h_193112)))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
            let _chain_wd_188155_4 := _chain_wd_188155_3
            let _chain_wd_188155_5 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
            let _wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
              let _wd_1_1 := _object_w336;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                let _atomic_wd_1_0 := (_object_w77 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w336
                exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w336).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_188693
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_194313 (show @Eq M.Value _ _ from Eq.refl _) h_193112)))))
            exact ((by
              let _equal_wd_1_0 := _chain_wd_188155_0
              let _equal_wd_1_1 := _chain_wd_188155_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
              let _equal_wd_1_0 := _chain_wd_188155_2
              let _equal_wd_1_1 := _chain_wd_188155_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_188155_4
              let _equal_wd_1_1 := _chain_wd_188155_5
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_188155_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_188693 True.intro);
                    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_188693 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_188693 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                    let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
                    (Litex.div _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _arithmetic := _atomic_wd_1_0
                        exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
                    let _chain_wd_188155_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_189580));
                    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (Litex.inRPos_real _object_i36 h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                    let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
                    (Litex.div _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_power := _atomic_wd_1_0
                        have _elaborated_power_base := (Litex.mulInC _wd_1_1 _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_189580))
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                      )) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
                    let _chain_wd_188155_2 := _chain_wd_188155_1
                    let _chain_wd_188155_3 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (16 : ℂ));
                    let _wd_2_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (16 : ℂ)) (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
                      let _wd_1_1 := _object_w336;
                      (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                        let _atomic_wd_1_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_194313 (show @Eq M.Value _ _ from Eq.refl _) h_193112)))));
                    let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
                    (Litex.div _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC (Litex.number (M := M) (16 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (16 : ℂ)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
                      let _wd_1_1 := _object_w336;
                      (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                        let _atomic_wd_1_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (_atomic_wd_1_0).val.right (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_194313 (show @Eq M.Value _ _ from Eq.refl _) h_193112)))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
                    let _chain_wd_188155_4 := _chain_wd_188155_3
                    let _chain_wd_188155_5 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
                    let _wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
                      let _wd_1_1 := _object_w336;
                      (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                        let _atomic_wd_1_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_194313 (show @Eq M.Value _ _ from Eq.refl _) h_193112)))))
                    exact (And.intro (congrArg₂ M.divValue (show (M.powValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (Litex.denote _value_i35)) (M.number (2 : ℂ))) = (M.powValue (M.mulValue (M.number (4 : ℂ)) (Litex.denote _object_i36)) (M.number (2 : ℂ))) from (congrArg₂ M.powValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (Litex.denote _value_i35)) = (M.mulValue (M.number (4 : ℂ)) (Litex.denote _object_i36)) from h_190505) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.number (4 : ℂ)) = (M.number (4 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _))) (And.intro (let _equal_wd_1_0 := _chain_wd_188155_2;
                    let _equal_wd_1_1 := _chain_wd_188155_3;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (congrArg₂ M.divValue (show (M.powValue (M.mulValue (M.number (4 : ℂ)) (Litex.denote _object_i36)) (M.number (2 : ℂ))) = (M.mulValue (M.number (16 : ℂ)) (M.powValue (Litex.denote _object_i36) (M.number (2 : ℂ)))) from (let _equal_wd_2_0 := (_equal_wd_1_0).val.left;
                    let _equal_wd_2_1 := (_equal_wd_1_1).val.left;
                    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((4 : ℂ) * (Litex.NativeBridge.asComplex _object_i36 (Litex.positiveRealToComplex _object_i36 h_189580))) ^ (2 : ℕ)) ((16 : ℂ) * ((Litex.NativeBridge.asComplex _object_i36 (Litex.positiveRealToComplex _object_i36 h_189580)) ^ (2 : ℕ))) (Litex.NativeBridge.denotePowNatReal (_equal_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                      let _atomic_wd_1_0 := (_equal_wd_2_0).val.base
                      exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (Litex.inRPos_real _object_i36 h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_189580) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.asComplex_spec _object_i36 (Litex.positiveRealToComplex _object_i36 h_189580)))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (16 : ℂ)) (_equal_wd_2_1).val.right (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ)) (Litex.NativeBridge.denotePowNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _object_i36 (Litex.positiveRealToComplex _object_i36 h_189580)))) (by ring!))))) (show (M.number (4 : ℂ)) = (M.number (4 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _))))) (let _equal_wd_1_0 := _chain_wd_188155_4;
                    let _equal_wd_1_1 := _chain_wd_188155_5;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((16 : ℂ) * ((Litex.NativeBridge.asComplex _object_i36 (Litex.positiveRealToComplex _object_i36 h_189580)) ^ (2 : ℕ))) / (4 : ℂ)) ((4 : ℂ) * ((Litex.NativeBridge.asComplex _object_i36 (Litex.positiveRealToComplex _object_i36 h_189580)) ^ (2 : ℕ))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_0).val.left (Litex.number (M := M) (4 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (16 : ℂ)) ((_equal_wd_1_0).val.left).val.right ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ)) (Litex.NativeBridge.denotePowNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _object_i36 (Litex.positiveRealToComplex _object_i36 h_189580)))) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.numberInC (M := M) (4 : ℂ)) (by
                      let _atomic_wd_1_0 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                      exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
                      let _wd_1_1 := _object_w336;
                      (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                        let _atomic_wd_1_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_194313 (show @Eq M.Value _ _ from Eq.refl _) h_193112))) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denotePowNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _object_i36 (Litex.positiveRealToComplex _object_i36 h_189580)))) (by
                      have _litex_nz_0 : ((4 : ℂ) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (Litex.number (M := M) (4 : ℂ)) (4 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
                      litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                    )))))))
                )
            )

          have h_226581 :=
            (And.left h_188155)

          have h_226582 :=
            (And.left (And.right h_188155))

          have h_226583 :=
            (And.right (And.right h_188155))

          have h_226584 :=
            h_226581

          have h_226585 :=
            h_226582

          have h_228062 : Litex.Same (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_189580));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (Litex.inRPos_real _object_i36 h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (let _wd_1_0 := (Litex.number (M := M) (16 : ℂ));
          let _wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (16 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
            let _wd_1_1 := _object_w336;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w336
              exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w336).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_188693
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
              let _atomic_wd_1_0 := (_object_w77 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w336
              exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w336).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_188693
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w336
              exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w336).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_188693
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_194313 (show @Eq M.Value _ _ from Eq.refl _) h_193112))))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.divCancelCommonDenominator (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_189580));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (Litex.inRPos_real _object_i36 h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (let _wd_1_0 := (Litex.number (M := M) (16 : ℂ));
                  let _wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                  (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (16 : ℂ)) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
                    let _wd_1_1 := _object_w336;
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                      let _atomic_wd_1_0 := (_object_w77 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_194313 (show @Eq M.Value _ _ from Eq.refl _) h_193112))))) (Litex.number (M := M) (4 : ℂ)) (by
                    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_189580));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_2_0 := _wd_1_0
                      exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (Litex.inRPos_real _object_i36 h_189580))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    exact (by
                      let _litex_power := _atomic_wd_1_0
                      have _elaborated_power_base := (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_189580))
                      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                    )) (by
                    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (16 : ℂ));
                    let _wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_189580) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (16 : ℂ)) (by
                      let _atomic_wd_2_0 := _wd_1_1
                      exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
                      let _wd_1_1 := _object_w336;
                      (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                        let _atomic_wd_1_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                        let _atomic_wd_1_0 := _object_w336
                        exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                          let _litex_power := (_object_w336).val.left
                          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          have _elaborated_power_exponent := h_188693
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_2_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_194313 (show @Eq M.Value _ _ from Eq.refl _) h_193112)))))
                    exact (Litex.mulInC (Litex.number (M := M) (16 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (16 : ℂ)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.inOfSame (let _wd_1_0 := (_object_w77 (M := M));
                    let _wd_1_1 := _object_w336;
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                      let _atomic_wd_1_0 := (_object_w77 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                      let _atomic_wd_1_0 := _object_w336
                      exact (Litex.mulInN (_object_w336).val.left (Litex.number (M := M) (2 : ℂ)) (by
                        let _litex_power := (_object_w336).val.left
                        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                        have _elaborated_power_exponent := h_188693
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (_atomic_wd_1_0).val.right (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_194313 (show @Eq M.Value _ _ from Eq.refl _) h_193112)))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_226585)
                )
            )

          have h_226586 :=
            h_226583

          have h_228063 :=
            (Eq.trans h_226581 h_226582)

          have h_228064 :=
            (Eq.trans (Eq.trans h_226581 h_226582) h_226583)

          have h_228065 :=
            (Eq.trans h_226582 h_226583)
          exact ((h_197813).trans (h_228064).symm)
        )
      )
  )

theorem h_228605 : ∀ {_Host_i38 : Type v38} [_rep_i38 : Litex.Representation M _Host_i38] (_value_i38 : Litex.Obj (M := M) _Host_i38) (h_228638 : Litex.In _value_i38 (Litex.N (M := M))), (by
  let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i38 (h_10610 (M := M)) h_228638 True.intro)
  let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i38 (h_20132 (M := M)) h_228638 True.intro)
  exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i38 _rep_i38 _value_i38 h_228638
          have h_228639 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i38 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i38 h_228638)
                )
            )
          have h_228908 : Litex.In _value_i38 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_228638
                )
            )
          have h_228909 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i38 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i38 h_228908)
                )
            )
          have h_266994 : ∀ (_raw_i39 : M.Value) (h_228923 : M.mem _raw_i39 (M.standard .integer)) (h_228924 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i39 = M.number (_s : ℂ) ∧ _r ≤ _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) _raw_i39) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) _raw_i39) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _raw_i39 h_228923 h_228924
                    let _value_i39 := Litex.semanticObject (M := M) _raw_i39 (M.member_isSet h_228923)
                    have h_228975 : Litex.In _value_i39 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i39 h_228923 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                              have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_228924)
                          )
                      )
                    exact Litex.integerInductionFromZero (fun (_raw_i39 : M.Value) => (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) _raw_i39) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) _raw_i39) = M.number (_s : ℂ) ∧ _r ≤ _s)) (by
                      let _raw_i39 : M.Value := M.number 0
                      have h_229372 : M.mem _raw_i39 (M.standard .integer) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num))
                      let _value_i39 := Litex.semanticObject (M := M) _raw_i39 (M.member_isSet h_229372)
                      have h_229372 : Litex.In _value_i39 (Litex.Z (M := M)) := h_229372
                      have h_229373 : Litex.Same _value_i39 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by rfl)
                            )
                        )
                      let _object_w366 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_10028 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)

                      have h_228607 : (by
                        let _equal_wd_1_0 := _object_w366
                        exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (let _equal_wd_1_0 := _object_w366;
                              (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (by
                                let _checked_call := _equal_wd_1_0
                                have _checked_case_guard : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
                                have _selected_beta := (h_10030 (M := M)) _checked_call.val.argument _checked_call.wd.2.1 _checked_case_guard
                                exact _selected_beta.trans (show @Eq M.Value _ _ from Eq.refl _))))
                            )
                        )
                      let _object_w368 := (let _wd_1_0 := _object_w366;
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.inRPos_real _object_w366 (Litex.callInOutput _object_w366))) True.intro))

                      have h_228608 : (by
                        let _equal_wd_1_0 := _object_w368
                        let _equal_wd_1_1 := (_object_w74 (M := M))
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_228607)
                            )
                        )
                      have h_228609 : (by
                        let _equal_wd_1_0 := (_object_w74 (M := M))
                        let _equal_wd_1_1 := (_object_w75 (M := M))
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (h_21882 (M := M))
                            )
                        )
                      have h_228610 : (by
                        let _equal_wd_1_0 := _object_w368
                        let _equal_wd_1_1 := (_object_w75 (M := M))
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((h_228608).trans h_228609)
                            )
                        )
                      let _object_w369 := (let _wd_1_0 := _object_w368;
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (by
                          let _litex_return_call := _object_w368
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))

                      let _object_w370 := (let _wd_1_0 := (_object_w75 (M := M));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := (_object_w75 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_object_w75 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))))

                      have h_228611 : (by
                        let _equal_wd_1_0 := _object_w369
                        let _equal_wd_1_1 := _object_w370
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (congrArg (Litex.absValue (M := M)) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ)))) = (M.negValue (M.number (1 : ℂ))) from h_228610))
                            )
                        )
                      have h_228612 : (by
                        let _equal_wd_1_0 := _object_w370
                        exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (let _equal_wd_1_0 := _object_w370;
                              (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((|(-1 : ℝ)| : ℝ) : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteAbs (_object_w370).val.arg (_object_w370).wd (-1 : ℝ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_object_w75 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (((-1 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
                            )
                        )
                      have h_228613 : (by
                        let _chain_wd_228613_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)
                        let _chain_wd_228613_1 := _object_w369
                        let _chain_wd_228613_2 := _chain_wd_228613_1
                        let _chain_wd_228613_3 := _object_w370
                        let _chain_wd_228613_4 := _chain_wd_228613_3
                        exact ((by
                          let _equal_wd_1_0 := _chain_wd_228613_0
                          let _equal_wd_1_1 := _chain_wd_228613_1
                          exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
                          let _equal_wd_1_0 := _chain_wd_228613_2
                          let _equal_wd_1_1 := _chain_wd_228613_3
                          exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
                          let _equal_wd_1_0 := _chain_wd_228613_4
                          exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _chain_wd_228613_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)
                                let _chain_wd_228613_1 := _object_w369
                                let _chain_wd_228613_2 := _chain_wd_228613_1
                                let _chain_wd_228613_3 := _object_w370
                                let _chain_wd_228613_4 := _chain_wd_228613_3
                                exact (And.intro (let _equal_wd_1_0 := _chain_wd_228613_0;
                                let _equal_wd_1_1 := _chain_wd_228613_1;
                                (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.number (0 : ℂ))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ))))) from by
                                  have _litex_residual : (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ))))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ))))) := (show @Eq M.Value _ _ from Eq.refl _)
                                  exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.number (0 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.number (0 : ℂ))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ))))) from by
                                  let _litex_original := _equal_wd_1_0
                                  let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro))
                                  have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_10611 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                                  have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                                  exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (Litex.denote _litex_literal.val.argument) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ))))) from rfl))
                                ))).trans _litex_residual))) (And.intro h_228611 h_228612)))
                            )
                        )

                      have h_230047 :=
                        (And.left h_228613)

                      have h_230048 :=
                        (And.left (And.right h_228613))

                      have h_230049 :=
                        (And.right (And.right h_228613))

                      have h_230050 :=
                        h_230047

                      have h_230051 :=
                        h_230048

                      have h_230052 :=
                        h_230049

                      have h_230053 :=
                        (Eq.trans h_230047 h_230048)

                      have h_230054 :=
                        (Eq.trans (Eq.trans h_230047 h_230048) h_230049)

                      have h_230055 :=
                        (Eq.trans h_230048 h_230049)
                      have h_228614 : (by
                        let _chain_wd_228614_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)
                        let _chain_wd_228614_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
                        let _wd_1_1 := (let _wd_2_0 := (_object_w77 (M := M));
                        let _wd_2_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)));
                        (Litex.powNatReal _wd_2_0 _wd_2_1 (1 : ℕ) (by
                          let _atomic_wd_1_0 := (_object_w77 (M := M))
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                          let _atomic_wd_1_0 := _wd_2_1
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num))));
                        (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (_atomic_wd_1_0).val.exponent (1 : ℕ) (by
                            let _atomic_wd_2_0 := (_object_w77 (M := M))
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                            let _atomic_wd_2_0 := (_atomic_wd_1_0).val.exponent
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber (_atomic_wd_1_0).val.exponent (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))).trans (congrArg M.number (by norm_num : (((1 : ℂ) / (4 : ℂ)) ^ (1 : ℕ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ)))))))
                        let _chain_wd_228614_2 := _chain_wd_228614_1
                        let _chain_wd_228614_3 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
                        let _wd_1_1 := (_object_w77 (M := M));
                        (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                          let _atomic_wd_1_0 := (_object_w77 (M := M))
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (4 : ℂ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ)))))))
                        let _chain_wd_228614_4 := _chain_wd_228614_3
                        exact ((by
                          let _equal_wd_1_0 := _chain_wd_228614_0
                          let _equal_wd_1_1 := _chain_wd_228614_1
                          exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
                          let _equal_wd_1_0 := _chain_wd_228614_2
                          let _equal_wd_1_1 := _chain_wd_228614_3
                          exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
                          let _equal_wd_1_0 := _chain_wd_228614_4
                          exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _chain_wd_228614_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)
                                let _chain_wd_228614_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
                                let _wd_1_1 := (let _wd_2_0 := (_object_w77 (M := M));
                                let _wd_2_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)));
                                (Litex.powNatReal _wd_2_0 _wd_2_1 (1 : ℕ) (by
                                  let _atomic_wd_1_0 := (_object_w77 (M := M))
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                                  let _atomic_wd_1_0 := _wd_2_1
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num))));
                                (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                                  let _atomic_wd_1_0 := _wd_1_1
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (_atomic_wd_1_0).val.exponent (1 : ℕ) (by
                                    let _atomic_wd_2_0 := (_object_w77 (M := M))
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                                    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.exponent
                                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber (_atomic_wd_1_0).val.exponent (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))).trans (congrArg M.number (by norm_num : (((1 : ℂ) / (4 : ℂ)) ^ (1 : ℕ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ)))))))
                                let _chain_wd_228614_2 := _chain_wd_228614_1
                                let _chain_wd_228614_3 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
                                let _wd_1_1 := (_object_w77 (M := M));
                                (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                                  let _atomic_wd_1_0 := (_object_w77 (M := M))
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (4 : ℂ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ)))))))
                                let _chain_wd_228614_4 := _chain_wd_228614_3
                                exact (And.intro (let _equal_wd_1_0 := _chain_wd_228614_0;
                                let _equal_wd_1_1 := _chain_wd_228614_1;
                                (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.number (0 : ℂ))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (0 : ℂ))))) from by
                                  have _litex_residual : (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (0 : ℂ))))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (0 : ℂ))))) := (show @Eq M.Value _ _ from Eq.refl _)
                                  exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.number (0 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.number (0 : ℂ))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (0 : ℂ))))) from by
                                  let _litex_original := _equal_wd_1_0
                                  let _litex_literal := (let _wd_1_0 := (_object_i15 (M := M));
                                  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                                  (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro))
                                  have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_20133 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                                  have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                                  exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (0 : ℂ))))) from rfl))
                                ))).trans _litex_residual))) (And.intro (let _equal_wd_1_0 := _chain_wd_228614_2;
                                let _equal_wd_1_1 := _chain_wd_228614_3;
                                (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((4 : ℂ) * (((1 : ℂ) / (4 : ℂ)) ^ (1 : ℕ))) ((4 : ℂ) * ((1 : ℂ) / (4 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.right).val.base ((_equal_wd_1_0).val.right).val.exponent (1 : ℕ) (by
                                  let _atomic_wd_1_0 := (_object_w77 (M := M))
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                                  let _atomic_wd_1_0 := ((_equal_wd_1_0).val.right).val.exponent
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber ((_equal_wd_1_0).val.right).val.exponent (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))) (by norm_num)))) (let _equal_wd_1_0 := _chain_wd_228614_4;
                                (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((4 : ℂ) * ((1 : ℂ) / (4 : ℂ))) (1 : ℂ) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))))))
                            )
                        )

                      have h_231883 :=
                        (And.left h_228614)

                      have h_231884 :=
                        (And.left (And.right h_228614))

                      have h_231885 :=
                        (And.right (And.right h_228614))

                      have h_231886 :=
                        h_231883

                      have h_231887 :=
                        h_231884

                      have h_232029 : Litex.Same (let _wd_1_0 := (_object_w77 (M := M));
                      let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)));
                      (Litex.powNatReal _wd_1_0 _wd_1_1 (1 : ℕ) (by
                        let _atomic_wd_1_0 := (_object_w77 (M := M))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)))) (_object_w77 (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.mulCancelLeftLeft (let _wd_1_0 := (_object_w77 (M := M));
                              let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)));
                              (Litex.powNatReal _wd_1_0 _wd_1_1 (1 : ℕ) (by
                                let _atomic_wd_1_0 := (_object_w77 (M := M))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                                let _atomic_wd_1_0 := _wd_1_1
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)))) (_object_w77 (M := M)) (Litex.number (M := M) (4 : ℂ)) (by
                                let _atomic_wd_1_0 := (let _wd_1_0 := (_object_w77 (M := M));
                                let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)));
                                (Litex.powNatReal _wd_1_0 _wd_1_1 (1 : ℕ) (by
                                  let _atomic_wd_2_0 := (_object_w77 (M := M))
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                                  let _atomic_wd_2_0 := _wd_1_1
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num))))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (_atomic_wd_1_0).val.exponent (1 : ℕ) (by
                                  let _atomic_wd_2_0 := (_object_w77 (M := M))
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                                  let _atomic_wd_2_0 := (_atomic_wd_1_0).val.exponent
                                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber (_atomic_wd_1_0).val.exponent (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))).trans (congrArg M.number (by norm_num : (((1 : ℂ) / (4 : ℂ)) ^ (1 : ℕ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ))))) (by
                                let _atomic_wd_1_0 := (_object_w77 (M := M))
                                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (4 : ℂ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_231887)
                            )
                        )

                      have h_231888 :=
                        h_231885

                      have h_232030 :=
                        (Eq.trans h_231883 h_231884)

                      have h_232031 :=
                        (Eq.trans (Eq.trans h_231883 h_231884) h_231885)

                      have h_232032 :=
                        (Eq.trans h_231884 h_231885)
                      show (fun (_raw_i39 : M.Value) => (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) _raw_i39) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) _raw_i39) = M.number (_s : ℂ) ∧ _r ≤ _s)) (M.number 0)
                      exact (by
                        let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)
                        let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)
                        exact (Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1 (h_230054).symm (h_232031).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
                    ) (by
                      intro _raw_i39 _induction_integer _induction_nonnegative _induction_hypothesis
                      have h_235219 : M.mem _raw_i39 (M.standard .integer) := _induction_integer
                      let _value_i39 := Litex.semanticObject (M := M) _raw_i39 (M.member_isSet h_235219)
                      have h_235219 : Litex.In _value_i39 (Litex.Z (M := M)) := h_235219
                      have h_235220 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i39 :=
                        (by
                          litex_checked_step =>
                            exact (
                              _induction_nonnegative
                            )
                        )
                      have h_235271 : Litex.In _value_i39 (Litex.N (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i39 h_235219 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_235220)
                            )
                        )
                      have h_228606 : Litex.Le (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) :=
                        (by
                          litex_checked_step =>
                            exact (
                              _induction_hypothesis
                            )
                        )
                      let _object_w385 := (let _wd_1_0 := (let _object_w379 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i39 (h_10028 (M := M)) h_235271 True.intro);
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w379 (h_96 (M := M)) (by
                        let _atomic_wd_1_0 := _object_w379
                        exact (Litex.inRPos_real _object_w379 (Litex.callInOutput _object_w379))) True.intro));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (by
                          let _litex_return_call := _atomic_wd_1_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))

                      have h_228615 : (by
                        let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                        let _equal_wd_1_1 := _object_w385
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                              let _equal_wd_1_1 := _object_w385;
                              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i39)) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i39)))) from by
                                have _litex_residual : (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i39)))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i39)))) := (show @Eq M.Value _ _ from Eq.refl _)
                                exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i39)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i39)) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i39)))) from by
                                let _litex_original := _equal_wd_1_0
                                let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
                                let _wd_1_1 := _value_i39;
                                (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_235271 True.intro))
                                have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_10611 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                                have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                                exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (Litex.denote _litex_literal.val.argument) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i39)))) from rfl))
                              ))).trans _litex_residual)))
                            )
                        )
                      have h_228616 : (by
                        let _atomic_wd_1_0 := _object_w385
                        exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := _object_w385
                                exact (by
                                  let _atomic_wd_2_1 := _atomic_wd_1_0
                                  exact (by
                                    let _litex_abs := _atomic_wd_2_1
                                    exact Litex.absNonnegative _litex_abs.val.arg _litex_abs.wd
                                  )))
                            )
                        )
                      have h_228617 : (by
                        let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                        exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                                exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w385 _atomic_wd_1_0 (show @Eq M.Value _ _ from Eq.refl _) (h_228615).symm h_228616))
                            )
                        )
                      have h_228618 : (by
                        let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)
                        exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)
                                exact (Litex.inRPos_positive _atomic_wd_1_0 (by
                                  let _atomic_wd_2_0 := _atomic_wd_1_0
                                  exact (by
                                    let _litex_return_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))))
                            )
                        )
                      have h_228619 : (by
                        let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)
                        exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)
                                exact (Litex.leTrans (Litex.number (M := M) (0 : ℂ)) (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro) _atomic_wd_1_1 h_228617 h_228606))
                            )
                        )
                      have h_228620 : (by
                        let _atomic_wd_1_1 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                        exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_1 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                                exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w385 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_228615).symm h_228616))
                            )
                        )
                      let _object_w386 := (let _wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                      let _wd_1_1 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                      (Litex.sub _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.positiveRealToComplex (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)))) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.realToComplex (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro))))))

                      have h_228621 : (by
                        let _atomic_wd_1_0 := _object_w386
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := _object_w386
                                exact (by
                                  let _litex_real_result := _atomic_wd_1_0
                                  exact Litex.subInR _litex_real_result.val.left _litex_real_result.val.right (by
                                  let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                  exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)))) (by
                                  let _atomic_wd_2_0 := (_atomic_wd_1_0).val.right
                                  exact (by
                                    let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
                                ))
                            )
                        )
                      let _object_w388 := (let _wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                      let _wd_1_1 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                      (Litex.add _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.positiveRealToComplex (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)))) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.realToComplex (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro))))))

                      have h_228622 : (by
                        let _atomic_wd_1_0 := _object_w388
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := _object_w388
                                exact (by
                                  let _litex_real_result := _atomic_wd_1_0
                                  exact Litex.addInR _litex_real_result.val.left _litex_real_result.val.right (by
                                  let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                  exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)))) (by
                                  let _atomic_wd_2_0 := (_atomic_wd_1_0).val.right
                                  exact (by
                                    let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
                                ))
                            )
                        )
                      have h_228623 : (by
                        let _atomic_wd_1_0 := _object_w386
                        exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := _object_w386
                                exact (Litex.subNonnegative _atomic_wd_1_0 (by
                                  let _atomic_wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                                  let _atomic_wd_2_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)
                                  exact h_228606)))
                            )
                        )
                      have h_228624 : (by
                        let _atomic_wd_1_0 := _object_w388
                        exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := _object_w388
                                exact (by
                                  let _litex_zero_bound := _atomic_wd_1_0
                                  exact Litex.addNonnegative _litex_zero_bound.val.left _litex_zero_bound.val.right _litex_zero_bound.wd.1 _litex_zero_bound.wd.2 (by
                                  let _atomic_wd_2_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)
                                  exact h_228619) (by
                                  let _atomic_wd_2_1 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                                  exact h_228620)
                                ))
                            )
                        )
                      have h_228625 : (by
                        let _atomic_wd_1_1 := _object_w386
                        exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_1 := _object_w386
                                exact h_228623)
                            )
                        )
                      have h_228626 : (by
                        let _atomic_wd_1_1 := _object_w388
                        exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_1 := _object_w388
                                exact h_228624)
                            )
                        )
                      let _object_w389 := (let _wd_1_0 := _object_w386;
                      let _wd_1_1 := _object_w388;
                      (Litex.mul _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (M.real_subset_complex _ h_228621)) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (M.real_subset_complex _ h_228622))))

                      have h_228627 : (by
                        let _atomic_wd_1_0 := _object_w389
                        exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := _object_w389
                                exact (by
                                  let _litex_zero_bound := _atomic_wd_1_0
                                  exact Litex.mulNonnegative _litex_zero_bound.val.left _litex_zero_bound.val.right _litex_zero_bound.wd.1 _litex_zero_bound.wd.2 (by
                                  let _atomic_wd_2_1 := (_atomic_wd_1_0).val.left
                                  exact h_228625) (by
                                  let _atomic_wd_2_1 := (_atomic_wd_1_0).val.right
                                  exact h_228626)
                                ))
                            )
                        )
                      have h_228628 : (by
                        let _chain_wd_228628_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                          let _atomic_wd_1_0 := _wd_2_0
                          exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                        let _wd_1_1 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                          let _atomic_wd_1_0 := _wd_2_0
                          exact (by
                            let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                        (Litex.sub _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (by
                            let _arithmetic := _atomic_wd_1_0
                            exact Litex.powObjInC _arithmetic)) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (by
                            let _arithmetic := _atomic_wd_1_0
                            exact Litex.powObjInC _arithmetic))))
                        let _chain_wd_228628_1 := _object_w389
                        exact ((by
                          let _equal_wd_1_0 := _chain_wd_228628_0
                          let _equal_wd_1_1 := _chain_wd_228628_1
                          exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
                          let _atomic_wd_1_0 := _chain_wd_228628_1
                          exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _chain_wd_228628_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                                let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                                  let _atomic_wd_1_0 := _wd_2_0
                                  exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                                let _wd_1_1 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                                let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                                  let _atomic_wd_1_0 := _wd_2_0
                                  exact (by
                                    let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                                (Litex.sub _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (by
                                    let _arithmetic := _atomic_wd_1_0
                                    exact Litex.powObjInC _arithmetic)) (by
                                  let _atomic_wd_1_0 := _wd_1_1
                                  exact (by
                                    let _arithmetic := _atomic_wd_1_0
                                    exact Litex.powObjInC _arithmetic))))
                                let _chain_wd_228628_1 := _object_w389
                                exact (And.intro (let _equal_wd_1_0 := _chain_wd_228628_0;
                                let _equal_wd_1_1 := _chain_wd_228628_1;
                                (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                                let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                                Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) ^ (2 : ℕ)) - ((let _litex_numeric_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                                let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                                Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) ^ (2 : ℕ))) (((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                                let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                                Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) - (let _litex_numeric_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                                let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                                Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member)) * ((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                                let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                                Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (let _litex_numeric_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                                let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                                Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member))) (Litex.NativeBridge.denoteSub (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                                  let _atomic_wd_1_0 := ((_equal_wd_1_0).val.left).val.base
                                  exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                                let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                                Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                                  let _atomic_wd_1_0 := ((_equal_wd_1_0).val.right).val.base
                                  exact (by
                                    let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _litex_numeric_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                                let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                                Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member))) (Litex.NativeBridge.denoteMul (_object_w389).val.left (_object_w389).val.right (by
                                  let _atomic_wd_1_0 := (_object_w389).val.left
                                  exact (M.real_subset_complex _ h_228621)) (by
                                  let _atomic_wd_1_0 := (_object_w389).val.right
                                  exact (M.real_subset_complex _ h_228622)) _ _ (Litex.NativeBridge.denoteSub (_object_w386).val.left (_object_w386).val.right (_object_w386).wd.1 (_object_w386).wd.2 _ _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                                let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                                Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (let _litex_numeric_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                                let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                                Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denoteAdd (_object_w388).val.left (_object_w388).val.right (_object_w388).wd.1 (_object_w388).wd.2 _ _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                                let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                                Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (let _litex_numeric_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                                let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                                Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member))) (by ring!)))) (by
                                  let _atomic_wd_1_0 := _chain_wd_228628_1
                                  exact h_228627)))
                            )
                        )

                      have h_245060 :=
                        (And.left h_228628)

                      have h_245061 :=
                        (And.right h_228628)

                      have h_245062 :=
                        h_245060

                      have h_245063 :=
                        h_245061

                      have h_245218 :=
                        (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w389 (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                          let _atomic_wd_1_0 := _wd_2_0
                          exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                        let _wd_1_1 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                          let _atomic_wd_1_0 := _wd_2_0
                          exact (by
                            let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                        (Litex.sub _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (by
                            let _arithmetic := _atomic_wd_1_0
                            exact Litex.powObjInC _arithmetic)) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (by
                            let _arithmetic := _atomic_wd_1_0
                            exact Litex.powObjInC _arithmetic)))) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (Eq.symm h_245060) h_245061)
                      have h_228629 : (by
                        let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                          let _atomic_wd_1_0 := _wd_2_0
                          exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                        let _wd_1_1 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                          let _atomic_wd_1_0 := _wd_2_0
                          exact (by
                            let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                        (Litex.sub _wd_1_0 _wd_1_1 (by
                          let _atomic_wd_1_0 := _wd_1_0
                          exact (by
                            let _arithmetic := _atomic_wd_1_0
                            exact Litex.powObjInC _arithmetic)) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (by
                            let _arithmetic := _atomic_wd_1_0
                            exact Litex.powObjInC _arithmetic))))
                        exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                                let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                                  let _atomic_wd_1_0 := _wd_2_0
                                  exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                                let _wd_1_1 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                                let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                                  let _atomic_wd_1_0 := _wd_2_0
                                  exact (by
                                    let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                                (Litex.sub _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (by
                                    let _arithmetic := _atomic_wd_1_0
                                    exact Litex.powObjInC _arithmetic)) (by
                                  let _atomic_wd_1_0 := _wd_1_1
                                  exact (by
                                    let _arithmetic := _atomic_wd_1_0
                                    exact Litex.powObjInC _arithmetic))))
                                exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w389 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_245060).symm h_228627))
                            )
                        )
                      let _object_w391 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                      (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (by
                          let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

                      let _object_w392 := (let _wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                      (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

                      have h_228630 : (by
                        let _atomic_wd_1_0 := _object_w391
                        let _atomic_wd_1_1 := _object_w392
                        exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := _object_w391
                                let _atomic_wd_1_1 := _object_w392
                                exact (Litex.subNonnegativeToLe (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro);
                                let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                                  let _atomic_wd_1_0 := _wd_2_0
                                  exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                                let _wd_1_1 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro);
                                let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                                  let _atomic_wd_1_0 := _wd_2_0
                                  exact (by
                                    let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                                (Litex.sub _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (by
                                    let _arithmetic := _atomic_wd_1_0
                                    exact Litex.powObjInC _arithmetic)) (by
                                  let _atomic_wd_1_0 := _wd_1_1
                                  exact (by
                                    let _arithmetic := _atomic_wd_1_0
                                    exact Litex.powObjInC _arithmetic)))) (by
                                  let _atomic_wd_2_0 := _atomic_wd_1_1
                                  exact (Litex.powStructuralInR _atomic_wd_2_0 (by
                                    let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
                                    exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)))))) (by
                                  let _atomic_wd_2_0 := _atomic_wd_1_0
                                  exact (Litex.powStructuralInR _atomic_wd_2_0 (by
                                    let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
                                    exact (by
                                      let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))))) h_228629))
                            )
                        )
                      have h_228631 : (by
                        let _atomic_wd_1_0 := _object_w391
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := _object_w391
                                exact (Litex.powStructuralInR _atomic_wd_1_0 (by
                                  let _atomic_wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                                  exact (by
                                    let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_235271 True.intro)
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
                            )
                        )
                      have h_228632 : (by
                        let _atomic_wd_1_0 := _object_w392
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := _object_w392
                                exact (Litex.powStructuralInR _atomic_wd_1_0 (by
                                  let _atomic_wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro)
                                  exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_235271 True.intro))))))
                            )
                        )
                      have h_228633 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
                            )
                        )
                      let _object_w394 := (let _wd_1_0 := _object_w391;
                      let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
                      (Litex.div _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (M.real_subset_complex _ h_228631)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

                      let _object_w395 := (let _wd_1_0 := _object_w392;
                      let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
                      (Litex.div _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (M.real_subset_complex _ h_228632)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

                      have h_228634 : (by
                        let _atomic_wd_1_0 := _object_w394
                        let _atomic_wd_1_1 := _object_w395
                        exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := _object_w394
                                let _atomic_wd_1_1 := _object_w395
                                exact (by
                                  let _litex_monotone_left := _atomic_wd_1_0
                                  let _litex_monotone_right := _atomic_wd_1_1
                                  exact Litex.divStructuralLe _litex_monotone_left _litex_monotone_right ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
                                  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                    apply Complex.ofReal_injective
                                    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                                    apply Complex.ofReal_injective
                                    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                                  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (by
                                  let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                                  let _atomic_wd_2_1 := (_atomic_wd_1_1).val.left
                                  exact h_228630) (Litex.sameRefl _litex_monotone_left.val.right)
                                ))
                            )
                        )
                      have h_264517 : Litex.Le (let _object_w399 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                      (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w399 (h_10610 (M := M)) (by
                        let _atomic_wd_1_0 := _object_w399
                        exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) _object_w394 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                have h_264516 : Litex.In _value_i39 (Litex.N (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        h_235271
                                      )
                                  )
                                have h_264526 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i39 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.naturalNonnegative _value_i39 h_264516)
                                      )
                                  )
                                exact ((h_147900 (M := M)) _value_i39 h_264516)
                              )
                            )
                        )
                      have h_228635 : (by
                        let _atomic_wd_1_0 := (let _object_w399 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                        (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w399 (h_10610 (M := M)) (by
                          let _atomic_wd_1_0 := _object_w399
                          exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                        let _atomic_wd_1_1 := _object_w394
                        exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _atomic_wd_1_0 := (let _object_w399 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                                (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w399 (h_10610 (M := M)) (by
                                  let _atomic_wd_1_0 := _object_w399
                                  exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                                let _atomic_wd_1_1 := _object_w394
                                exact h_264517)
                            )
                        )
                      have h_266209 : Litex.Same (let _object_w402 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                      (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w402 (h_20132 (M := M)) (by
                        let _atomic_wd_1_0 := _object_w402
                        exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) _object_w395 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                have h_266208 : Litex.In _value_i39 (Litex.N (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        h_235271
                                      )
                                  )
                                have h_266218 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i39 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.naturalNonnegative _value_i39 h_266208)
                                      )
                                  )
                                exact ((h_188148 (M := M)) _value_i39 h_266208)
                              )
                            )
                        )
                      have h_228636 : (by
                        let _equal_wd_1_0 := (let _object_w402 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                        (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w402 (h_20132 (M := M)) (by
                          let _atomic_wd_1_0 := _object_w402
                          exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                        let _equal_wd_1_1 := _object_w395
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              h_266209
                            )
                        )
                      have h_228637 : (by
                        let _chain_wd_228637_4 := _object_w395
                        let _chain_wd_228637_5 := (let _object_w402 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                        (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w402 (h_20132 (M := M)) (by
                          let _atomic_wd_1_0 := _object_w402
                          exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                        exact ((by
                          let _atomic_wd_1_0 := (let _object_w399 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                          (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w399 (h_10610 (M := M)) (by
                            let _atomic_wd_1_0 := _object_w399
                            exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                          let _atomic_wd_1_1 := _object_w394
                          exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)) ∧ (((by
                          let _atomic_wd_1_0 := _object_w394
                          let _atomic_wd_1_1 := _object_w395
                          exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)) ∧ ((by
                          let _equal_wd_1_0 := _chain_wd_228637_4
                          let _equal_wd_1_1 := _chain_wd_228637_5
                          exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                let _chain_wd_228637_4 := _object_w395
                                let _chain_wd_228637_5 := (let _object_w402 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                                (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w402 (h_20132 (M := M)) (by
                                  let _atomic_wd_1_0 := _object_w402
                                  exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                                exact (And.intro (by
                                  let _atomic_wd_1_0 := (let _object_w399 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                                  (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w399 (h_10610 (M := M)) (by
                                    let _atomic_wd_1_0 := _object_w399
                                    exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                                  let _atomic_wd_1_1 := _object_w394
                                  exact h_264517) (And.intro (by
                                  let _atomic_wd_1_0 := _object_w394
                                  let _atomic_wd_1_1 := _object_w395
                                  exact h_228634) (h_266209).symm)))
                            )
                        )

                      have h_266586 :=
                        (And.left h_228637)

                      have h_266587 :=
                        (And.left (And.right h_228637))

                      have h_266588 :=
                        (And.right (And.right h_228637))

                      have h_266589 :=
                        h_266586

                      have h_266590 :=
                        h_266587

                      have h_266591 :=
                        h_266588

                      have h_266956 :=
                        (Litex.leTrans (let _object_w399 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                        (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w399 (h_10610 (M := M)) (by
                          let _atomic_wd_1_0 := _object_w399
                          exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) _object_w394 _object_w395 h_266586 h_266587)

                      have h_266957 :=
                        (Litex.leOfSame (let _object_w399 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                        (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w399 (h_10610 (M := M)) (by
                          let _atomic_wd_1_0 := _object_w399
                          exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) (let _object_w399 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                        (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w399 (h_10610 (M := M)) (by
                          let _atomic_wd_1_0 := _object_w399
                          exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) _object_w395 (let _object_w402 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                        (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w402 (h_20132 (M := M)) (by
                          let _atomic_wd_1_0 := _object_w402
                          exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) (Litex.sameRefl (let _object_w399 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                        (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w399 (h_10610 (M := M)) (by
                          let _atomic_wd_1_0 := _object_w399
                          exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))) h_266588 (Litex.leTrans (let _object_w399 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                        (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w399 (h_10610 (M := M)) (by
                          let _atomic_wd_1_0 := _object_w399
                          exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) _object_w394 _object_w395 h_266586 h_266587))

                      have h_266958 :=
                        (Litex.leOfSame _object_w394 _object_w394 _object_w395 (let _object_w402 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                        (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w402 (h_20132 (M := M)) (by
                          let _atomic_wd_1_0 := _object_w402
                          exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) (Litex.sameRefl _object_w394) h_266588 h_266587)
                      show (fun (_raw_i39 : M.Value) => (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) _raw_i39) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) _raw_i39) = M.number (_s : ℂ) ∧ _r ≤ _s)) (M.addValue _raw_i39 (M.number 1))
                      exact (by
                        let _atomic_wd_1_0 := (let _object_w399 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                        (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w399 (h_10610 (M := M)) (by
                          let _atomic_wd_1_0 := _object_w399
                          exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                        let _atomic_wd_1_1 := (let _object_w402 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_235219) (Litex.numberInC (M := M) (1 : ℂ)));
                        (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w402 (h_20132 (M := M)) (by
                          let _atomic_wd_1_0 := _object_w402
                          exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_235271 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                        exact (Litex.leOfSame _atomic_wd_1_0 _atomic_wd_1_0 _object_w395 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_266209).symm h_266956))
                    ) _value_i39 h_228923 h_228924
                  )
                )
            )
          exact (by
            let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i38 (h_10610 (M := M)) h_228908 True.intro)
            let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i38 (h_20132 (M := M)) h_228908 True.intro)
            exact (by
              have h_270395 : Litex.In _value_i38 (Litex.Z (M := M)) :=
                (Litex.naturalToInteger _value_i38 h_228908)
              have h_270420 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i38 :=
                h_228909
              exact (Litex.leOfSame _atomic_wd_1_0 _atomic_wd_1_0 _atomic_wd_1_1 _atomic_wd_1_1 (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i11 (M := M))) (Litex.sameRefl _value_i38)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i15 (M := M))) (Litex.sameRefl _value_i38)) ((fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value : Litex.Obj (M := M) _Host) => h_266994 (Litex.denote _value)) _value_i38 h_270395 h_270420))
            ))
        )
      )
  )

theorem h_270740 : Litex.Le (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_270739 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                )
            )
          have h_270751 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (2 : ℂ)) h_270739)
                )
            )
          exact ((h_228605 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_270739)
        )
      )
  )

theorem h_271334 : (by
  let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
  let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
  exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
          let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
          exact (h_270740 (M := M)))
      )
  )

noncomputable def _object_w412 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (64 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (64 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (64 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (64 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (64 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_271398 : (by
  let _equal_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
  let _equal_wd_1_1 := (_object_w412 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro);
        let _equal_wd_1_1 := (_object_w412 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.number (2 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (64 : ℂ))) from by
          have _litex_residual : (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (2 : ℂ))))) = (M.divValue (M.number (1 : ℂ)) (M.number (64 : ℂ))) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
          let _wd_1_1 := (let _wd_2_0 := (_object_w77 (M := M));
          let _wd_2_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (4 : ℕ) (by
            let _atomic_wd_1_0 := (_object_w77 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (2 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (2 : ℕ)) (4 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((4 : ℕ) : ℂ)) ((2 : ℂ) ^ (2 : ℕ)) ((4 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((4 : ℕ) : ℂ)) (by norm_num))));
          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (256 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (_atomic_wd_1_0).val.exponent (4 : ℕ) (by
              let _atomic_wd_2_0 := (_object_w77 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_2_0 := (_atomic_wd_1_0).val.exponent
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (2 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (2 : ℕ)) (4 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber (_atomic_wd_1_0).val.exponent (Litex.number (M := M) ((4 : ℕ) : ℂ)) ((2 : ℂ) ^ (2 : ℕ)) ((4 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((4 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))).trans (congrArg M.number (by norm_num : (((1 : ℂ) / (4 : ℂ)) ^ (4 : ℕ)) = ((1 : ℂ) / (256 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (256 : ℂ)))))));
          let _equal_wd_2_1 := _equal_wd_1_1;
          (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 ((4 : ℂ) * (((1 : ℂ) / (4 : ℂ)) ^ (4 : ℕ))) ((1 : ℂ) / (64 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denotePowNatReal ((_equal_wd_2_0).val.right).val.base ((_equal_wd_2_0).val.right).val.exponent (4 : ℕ) (by
            let _atomic_wd_1_0 := (_object_w77 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
            let _atomic_wd_1_0 := ((_equal_wd_2_0).val.right).val.exponent
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (2 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (2 : ℕ)) (4 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber ((_equal_wd_2_0).val.right).val.exponent (Litex.number (M := M) ((4 : ℕ) : ℂ)) ((2 : ℂ) ^ (2 : ℕ)) ((4 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((4 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w77 (M := M))).wd.1 ((_object_w77 (M := M))).wd.2.1 ((_object_w77 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (64 : ℂ)) (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2.1 (_equal_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (64 : ℂ))) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.number (2 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.number (2 : ℂ))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (2 : ℂ))))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i15 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_20133 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (2 : ℂ))))) from rfl))
        ))).trans _litex_residual)))
      )
  )

theorem h_271882 : (by
  let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
  let _atomic_wd_1_1 := (_object_w412 (M := M))
  exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
          let _atomic_wd_1_1 := (_object_w412 (M := M))
          exact (Litex.leOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_271398 (M := M)) (h_270740 (M := M))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_newton_x5f_residual_x5f_bound_x2f_statement_x2e_lit
