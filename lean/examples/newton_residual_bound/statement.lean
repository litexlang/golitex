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
  (Litex.formulaFnInFnSet (_object_i1 (M := M)))
theorem h_97 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (Litex.sameRefl (_object_i1 (M := M)))

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
    let _object_w8 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i3 h_365) h_368)

    have h_102 : (by
      let _atomic_wd_1_0 := _object_w8
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w8
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
    let _object_w9 := (let _wd_1_0 := _value_i3;
    let _wd_1_1 := _object_w8;
    (Litex.add _wd_1_0 _wd_1_1 (Litex.positiveRealToComplex _wd_1_0 h_365) (by
      let _atomic_wd_1_0 := _object_w8
      exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_1_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_1_0 h_365) (_atomic_wd_1_0).wd.2.2))))

    have h_103 : (by
      let _atomic_wd_1_0 := _object_w9
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w9
              exact (by
                let _litex_positive_result := _atomic_wd_1_0
                exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 h_100 (by
                let _atomic_wd_2_0 := _object_w8
                exact h_102)
              ))
          )
      )
    let _object_w10 := (let _wd_1_0 := _object_w9;
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w9
      exact (Litex.addInC _value_i3 (_object_w9).val.right (Litex.positiveRealToComplex _value_i3 h_365) (Litex.divInC _wd_1_1 _value_i3 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i3 h_365) ((_object_w9).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

    have h_104 : (by
      let _atomic_wd_1_0 := _object_w10
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w10
              exact (by
                let _litex_positive_result := _atomic_wd_1_0
                exact Litex.divPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2.1 _litex_positive_result.wd.2.2 (by
                let _atomic_wd_2_1 := _object_w9
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
      let _atomic_wd_1_0 := _object_w10
      exact (Litex.inRPos_intro _atomic_wd_1_0 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_104; exact (M.real_members (Litex.denote _atomic_wd_1_0)).mpr ⟨_litex_real, _litex_value⟩) h_104))
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
  (Litex.formulaFnInFnSet (_object_i4 (M := M)))
theorem h_7460 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (Litex.sameRefl (_object_i4 (M := M)))

theorem h_7464 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_7466 : Litex.In _value_i6 (Litex.N (M := M))), ((Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6)) :=
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

theorem h_7614 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_7617 : Litex.In _value_i7 (Litex.N (M := M))) (h_7612 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7), Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i7 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i7 h_7617) (Litex.numberInC (M := M) (1 : ℂ))) :=
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
    let _object_w24 := (Litex.sub _value_i7 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i7 h_7738) (Litex.numberInC (M := M) (1 : ℂ)))

    have h_7615 : (by
      let _atomic_wd_1_0 := _object_w24
      exact Litex.In _atomic_wd_1_0 (Litex.N (M := M))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w24
              exact (Litex.predecessorInN _atomic_wd_1_0 h_7738 h_7612 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
          )
      )

    have h_7825 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w24 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _object_w24 h_7615)
          )
      )
    have h_7616 : (by
      let _atomic_wd_1_0 := _object_w24
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w24
              exact h_7825)
          )
      )
    exact (by
      let _atomic_wd_1_0 := _object_w24
      exact h_7616)
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
  have _checked_body := (let _object_w36 := (let _object_w35 := (Litex.sub _value_i9 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i9 h_7994) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i10 : M.Value) => (((∃ (_r _s : ℝ), _raw_i10 = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i10 = M.number (_s : ℂ) ∧ _r ≤ _s)))) _object_i8 _object_w35 h_8052 (by
    let _atomic_wd_1_0 := _object_w35
    exact (Litex.predecessorInN _atomic_wd_1_0 h_7994 h_7991 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))) (And.intro (by
    let _atomic_wd_1_0 := _object_w35
    exact (Litex.subtractOneLess _atomic_wd_1_0 (Litex.naturalToReal _value_i9 h_7994) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))) (by
    let _atomic_wd_1_0 := _object_w35
    exact (Litex.subNonnegative _atomic_wd_1_0 (Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _value_i9 _value_i9 ((Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))).symm (Litex.sameRefl _value_i9) (Litex.integerSuccessorLowerBound _value_i9 (Litex.naturalToInteger _value_i9 h_7994) h_7991)))))));
  (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _object_w36 (h_7459 (M := M)) (Litex.inRPos_real _object_w36 (by
    let _atomic_wd_1_0 := _object_w36
    exact (by
      let _litex_return_call := _object_w36
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w36)).mp (by
    let _atomic_wd_1_0 := _object_w36
    exact (by
      let _litex_return_call := _object_w36
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))).2))
  exact (by
    let _atomic_wd_1_0 := (let _object_w38 := (let _object_w37 := (Litex.sub _value_i9 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i9 h_7994) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i10 : M.Value) => (((∃ (_r _s : ℝ), _raw_i10 = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i10 = M.number (_s : ℂ) ∧ _r ≤ _s)))) _object_i8 _object_w37 h_8052 (by
      let _atomic_wd_2_0 := _object_w37
      exact (Litex.predecessorInN _atomic_wd_2_0 h_7994 h_7991 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))) (And.intro (by
      let _atomic_wd_2_0 := _object_w37
      exact (Litex.subtractOneLess _atomic_wd_2_0 (Litex.naturalToReal _value_i9 h_7994) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))) (by
      let _atomic_wd_2_0 := _object_w37
      exact (Litex.subNonnegative _atomic_wd_2_0 (Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _value_i9 _value_i9 ((Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))).symm (Litex.sameRefl _value_i9) (Litex.integerSuccessorLowerBound _value_i9 (Litex.naturalToInteger _value_i9 h_7994) h_7991)))))));
    (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _object_w38 (h_7459 (M := M)) (Litex.inRPos_real _object_w38 (by
      let _atomic_wd_2_0 := _object_w38
      exact (by
        let _litex_return_call := _object_w38
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w38)).mp (by
      let _atomic_wd_2_0 := _object_w38
      exact (by
        let _litex_return_call := _object_w38
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
theorem h_10028 : Litex.In (_object_i8 (M := M)) (by
  have _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.natural) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := by
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
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True))) :=
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
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _object_w43 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i12 (h_10028 (M := M)) h_10046 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w43 (h_96 (M := M)) (by
      let _atomic_wd_2_0 := _object_w43
      exact (Litex.inRPos_real _object_w43 (Litex.callInOutput _object_w43))) True.intro));
    (Litex.abs _wd_1_0 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_return_call := _atomic_wd_2_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (let _object_w43 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i12 (h_10028 (M := M)) h_10046 True.intro);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w43 (h_96 (M := M)) (by
      let _atomic_wd_2_0 := _object_w43
      exact (Litex.inRPos_real _object_w43 (Litex.callInOutput _object_w43))) True.intro));
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
  (Litex.formulaFnInFnSet (_object_i11 (M := M)))
theorem h_10611 : Litex.Same (_object_i11 (M := M)) (_object_i11 (M := M)) :=
  (Litex.sameRefl (_object_i11 (M := M)))

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
    let _object_w50 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) _value_i13 (Litex.NativeBridge.asNat _value_i13 h_10924) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_10924 (Litex.NativeBridge.asNat_spec _value_i13 h_10924))

    have h_10614 : (by
      let _atomic_wd_1_0 := _object_w50
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w50
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
    let _object_w52 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

    have h_10615 : (by
      let _atomic_wd_1_0 := _object_w52
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w52
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
    let _object_w54 := (let _wd_1_0 := _object_w52;
    let _wd_1_1 := _object_w50;
    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w50
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_10924
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      ))) (by
      let _atomic_wd_1_0 := _object_w52
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
      let _atomic_wd_1_0 := _object_w50
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_10924
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w50
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_10924
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      )))))

    have h_10616 : (by
      let _atomic_wd_1_0 := _object_w54
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w54
              exact (by
                let _atomic_wd_2_1 := _atomic_wd_1_0
                exact (Litex.powStructuralPositiveOfPositive _atomic_wd_2_1 (by
                  let _atomic_wd_3_1 := _object_w52
                  exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_3_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                    let _atomic_wd_4_0 := _object_w52
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_3_1 (by
                    let _atomic_wd_4_0 := _object_w52
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (4 : ℝ)) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_3_1 (by
                    let _atomic_wd_4_0 := _object_w52
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))))
          )
      )
    let _object_w55 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_1_1 := _object_w54;
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _object_w54
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.NativeBridge.inOfDenoteNumber (_object_w54).val.base ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (4 : ℂ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ))))
        have _elaborated_power_exponent := (by
        let _litex_power := (_object_w54).val.exponent
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
      let _atomic_wd_1_0 := _object_w55
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w55
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
                let _atomic_wd_2_1 := _object_w54
                exact h_10616)
              ))
          )
      )
    exact (by
      let _atomic_wd_1_0 := _object_w55
      exact (Litex.inRPos_intro _atomic_wd_1_0 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_10617; exact (M.real_members (Litex.denote _atomic_wd_1_0)).mpr ⟨_litex_real, _litex_value⟩) h_10617))
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
  (Litex.formulaFnInFnSet (_object_i15 (M := M)))
theorem h_20133 : Litex.Same (_object_i15 (M := M)) (_object_i15 (M := M)) :=
  (Litex.sameRefl (_object_i15 (M := M)))

noncomputable def _object_w61 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_7459 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (1 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))).2)

noncomputable def _object_w62 := (Litex.div (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_20134 : (by
  let _equal_wd_1_0 := (_object_w61 (M := M))
  let _equal_wd_1_1 := (_object_w62 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (let _equal_wd_1_0 := (_object_w61 (M := M));
  let _equal_wd_1_1 := (_object_w62 (M := M));
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
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (1 : ℂ))))).trans (by
    let _litex_original := _equal_wd_1_0
    let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))).2))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_7460 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (M.number (1 : ℂ)) (M.divValue (M.number (2 : ℂ)) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) from rfl))
  ))).trans _litex_residual)))

theorem h_20709 : (by
  let _chain_wd_20709_0 := (let _wd_1_0 := (_object_w62 (M := M));
  (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _wd_1_0 (h_7459 (M := M)) (Litex.inRPos_real _wd_1_0 (by
    let _atomic_wd_1_0 := (_object_w62 (M := M))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_0)).mp (by
    let _atomic_wd_1_0 := (_object_w62 (M := M))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))).2))
  let _chain_wd_20709_1 := (let _wd_1_0 := (let _wd_2_0 := (_object_w62 (M := M));
  let _wd_2_1 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_3_1 := (_object_w62 (M := M));
  (Litex.div _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
    let _atomic_wd_1_0 := (_object_w62 (M := M))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
    let _atomic_wd_1_0 := (_object_w62 (M := M))
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := (_object_w62 (M := M))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((4 : ℂ) / (3 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))).trans (congrArg M.number (by norm_num : ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ))) = ((4 : ℂ) / (3 : ℂ))))) (Litex.numberInC (M := M) ((4 : ℂ) / (3 : ℂ)))))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (6 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.right).val.right ((_atomic_wd_1_0).val.right).wd.1 ((_atomic_wd_1_0).val.right).wd.2.1 ((_atomic_wd_1_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))))).trans (congrArg M.number (by norm_num : (((3 : ℂ) / (2 : ℂ)) + ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ)))) = ((17 : ℂ) / (6 : ℂ))))) (Litex.numberInC (M := M) ((17 : ℂ) / (6 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
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
    let _chain_wd_20709_0 := (let _wd_1_0 := (_object_w62 (M := M));
    (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _wd_1_0 (h_7459 (M := M)) (Litex.inRPos_real _wd_1_0 (by
      let _atomic_wd_1_0 := (_object_w62 (M := M))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_0)).mp (by
      let _atomic_wd_1_0 := (_object_w62 (M := M))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))).2))
    let _chain_wd_20709_1 := (let _wd_1_0 := (let _wd_2_0 := (_object_w62 (M := M));
    let _wd_2_1 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
    let _wd_3_1 := (_object_w62 (M := M));
    (Litex.div _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
      let _atomic_wd_1_0 := (_object_w62 (M := M))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
      let _atomic_wd_1_0 := (_object_w62 (M := M))
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_1_0 := (_object_w62 (M := M))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((4 : ℂ) / (3 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))).trans (congrArg M.number (by norm_num : ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ))) = ((4 : ℂ) / (3 : ℂ))))) (Litex.numberInC (M := M) ((4 : ℂ) / (3 : ℂ)))))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (6 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.right).val.right ((_atomic_wd_1_0).val.right).wd.1 ((_atomic_wd_1_0).val.right).wd.2.1 ((_atomic_wd_1_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))))).trans (congrArg M.number (by norm_num : (((3 : ℂ) / (2 : ℂ)) + ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ)))) = ((17 : ℂ) / (6 : ℂ))))) (Litex.numberInC (M := M) ((17 : ℂ) / (6 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
    let _chain_wd_20709_2 := _chain_wd_20709_1
    let _chain_wd_20709_3 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact (And.intro (let _equal_wd_1_0 := _chain_wd_20709_0;
    let _equal_wd_1_1 := _chain_wd_20709_1;
    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ)))) = (M.divValue (M.addValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.divValue (M.number (2 : ℂ)) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))))) (M.number (2 : ℂ))) from by
      have _litex_residual : (M.divValue (M.addValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.divValue (M.number (2 : ℂ)) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))))) (M.number (2 : ℂ))) = (M.divValue (M.addValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.divValue (M.number (2 : ℂ)) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))))) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ)))))).trans (by
      let _litex_original := _equal_wd_1_0
      let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
      let _wd_1_1 := (_object_w62 (M := M));
      (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 (by
        let _atomic_wd_1_0 := (_object_w62 (M := M))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp (by
        let _atomic_wd_1_0 := (_object_w62 (M := M))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))).2))
      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_7460 (M := M)) (Litex.sameRefl _litex_original.val.argument)
      have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.divValue (M.number (2 : ℂ)) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))))) (M.number (2 : ℂ))) from rfl))
    ))).trans _litex_residual))) (let _equal_wd_1_0 := _chain_wd_20709_2;
    let _equal_wd_1_1 := _chain_wd_20709_3;
    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((((3 : ℂ) / (2 : ℂ)) + ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ)))) / (2 : ℂ)) ((17 : ℂ) / (12 : ℂ)) (Litex.NativeBridge.denoteDiv (_equal_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd ((_equal_wd_1_0).val.left).val.left ((_equal_wd_1_0).val.left).val.right ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (((_equal_wd_1_0).val.left).val.right).val.right (((_equal_wd_1_0).val.left).val.right).wd.1 (((_equal_wd_1_0).val.left).val.right).wd.2.1 (((_equal_wd_1_0).val.left).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (by norm_num))))))

theorem h_21877 : Litex.Same (let _wd_1_0 := (_object_w62 (M := M));
(Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _wd_1_0 (h_7459 (M := M)) (Litex.inRPos_real _wd_1_0 (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_0)).mp (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))).2)) (let _wd_1_0 := (let _wd_2_0 := (_object_w62 (M := M));
let _wd_2_1 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
let _wd_3_1 := (_object_w62 (M := M));
(Litex.div _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
(Litex.add _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := _wd_2_1
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((4 : ℂ) / (3 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))).trans (congrArg M.number (by norm_num : ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ))) = ((4 : ℂ) / (3 : ℂ))))) (Litex.numberInC (M := M) ((4 : ℂ) / (3 : ℂ)))))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (6 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.right).val.right ((_atomic_wd_1_0).val.right).wd.1 ((_atomic_wd_1_0).val.right).wd.2.1 ((_atomic_wd_1_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))))).trans (congrArg M.number (by norm_num : (((3 : ℂ) / (2 : ℂ)) + ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ)))) = ((17 : ℂ) / (6 : ℂ))))) (Litex.numberInC (M := M) ((17 : ℂ) / (6 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) :=
  (And.left (h_20709 (M := M)))

theorem h_21878 : Litex.Same (let _wd_1_0 := (let _wd_2_0 := (_object_w62 (M := M));
let _wd_2_1 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
let _wd_3_1 := (_object_w62 (M := M));
(Litex.div _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
(Litex.add _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := _wd_2_1
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((4 : ℂ) / (3 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))).trans (congrArg M.number (by norm_num : ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ))) = ((4 : ℂ) / (3 : ℂ))))) (Litex.numberInC (M := M) ((4 : ℂ) / (3 : ℂ)))))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (6 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.right).val.right ((_atomic_wd_1_0).val.right).wd.1 ((_atomic_wd_1_0).val.right).wd.2.1 ((_atomic_wd_1_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))))).trans (congrArg M.number (by norm_num : (((3 : ℂ) / (2 : ℂ)) + ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ)))) = ((17 : ℂ) / (6 : ℂ))))) (Litex.numberInC (M := M) ((17 : ℂ) / (6 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) :=
  (And.right (h_20709 (M := M)))

theorem h_21879 : Litex.Same (let _wd_1_0 := (_object_w62 (M := M));
(Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _wd_1_0 (h_7459 (M := M)) (Litex.inRPos_real _wd_1_0 (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_0)).mp (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))).2)) (let _wd_1_0 := (let _wd_2_0 := (_object_w62 (M := M));
let _wd_2_1 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
let _wd_3_1 := (_object_w62 (M := M));
(Litex.div _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
(Litex.add _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := _wd_2_1
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((4 : ℂ) / (3 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))).trans (congrArg M.number (by norm_num : ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ))) = ((4 : ℂ) / (3 : ℂ))))) (Litex.numberInC (M := M) ((4 : ℂ) / (3 : ℂ)))))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (6 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.right).val.right ((_atomic_wd_1_0).val.right).wd.1 ((_atomic_wd_1_0).val.right).wd.2.1 ((_atomic_wd_1_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))))).trans (congrArg M.number (by norm_num : (((3 : ℂ) / (2 : ℂ)) + ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ)))) = ((17 : ℂ) / (6 : ℂ))))) (Litex.numberInC (M := M) ((17 : ℂ) / (6 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) :=
  (h_21877 (M := M))

theorem h_21880 : Litex.Same (let _wd_1_0 := (let _wd_2_0 := (_object_w62 (M := M));
let _wd_2_1 := (let _wd_3_0 := (Litex.number (M := M) (2 : ℂ));
let _wd_3_1 := (_object_w62 (M := M));
(Litex.div _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((3 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
(Litex.add _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((3 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (2 : ℂ))))) (by
  let _atomic_wd_1_0 := _wd_2_1
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((4 : ℂ) / (3 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))).trans (congrArg M.number (by norm_num : ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ))) = ((4 : ℂ) / (3 : ℂ))))) (Litex.numberInC (M := M) ((4 : ℂ) / (3 : ℂ)))))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (6 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.right).val.right ((_atomic_wd_1_0).val.right).wd.1 ((_atomic_wd_1_0).val.right).wd.2.1 ((_atomic_wd_1_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))))).trans (congrArg M.number (by norm_num : (((3 : ℂ) / (2 : ℂ)) + ((2 : ℂ) / ((3 : ℂ) / (2 : ℂ)))) = ((17 : ℂ) / (6 : ℂ))))) (Litex.numberInC (M := M) ((17 : ℂ) / (6 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) :=
  (h_21878 (M := M))

theorem h_21881 : Litex.Same (let _wd_1_0 := (_object_w62 (M := M));
(Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _wd_1_0 (h_7459 (M := M)) (Litex.inRPos_real _wd_1_0 (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_0)).mp (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInRPosOfEq (M := M) ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num) (by norm_num))))).2)) (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) :=
  (Eq.trans (h_21877 (M := M)) (h_21878 (M := M)))

noncomputable def _object_w63 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_96 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)

noncomputable def _object_w64 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))

theorem h_21882 : (by
  let _equal_wd_1_0 := (_object_w63 (M := M))
  let _equal_wd_1_1 := (_object_w64 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (let _equal_wd_1_0 := (_object_w63 (M := M));
  let _equal_wd_1_1 := (_object_w64 (M := M));
  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ))) = (M.negValue (M.number (1 : ℂ))) from by
    have _litex_residual : (M.subValue (M.powValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) = (M.negValue (M.number (1 : ℂ))) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) ^ (2 : ℕ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ))));
    let _equal_wd_2_1 := _equal_wd_1_1;
    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 (((1 : ℂ) ^ (2 : ℕ)) - (2 : ℂ)) (- (1 : ℂ)) (Litex.NativeBridge.denoteSub (_equal_wd_2_0).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num))))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ))))).trans (by
    let _litex_original := _equal_wd_1_0
    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_97 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (M.powValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from rfl))
  ))).trans _litex_residual)))

noncomputable def _object_w65 := (let _wd_1_0 := (_object_w62 (M := M));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
  let _atomic_wd_1_0 := (_object_w62 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro))

noncomputable def _object_w66 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_22340 : (by
  let _equal_wd_1_0 := (_object_w65 (M := M))
  let _equal_wd_1_1 := (_object_w66 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (let _equal_wd_1_0 := (_object_w65 (M := M));
  let _equal_wd_1_1 := (_object_w66 (M := M));
  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ)))) = (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) from by
    have _litex_residual : (M.subValue (M.powValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) := (let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := (_object_w62 (M := M));
    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := (_object_w62 (M := M))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((9 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
        let _atomic_wd_2_0 := (_object_w62 (M := M))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))).trans (congrArg M.number (by norm_num : (((3 : ℂ) / (2 : ℂ)) ^ (2 : ℕ)) = ((9 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((9 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ))));
    let _equal_wd_2_1 := _equal_wd_1_1;
    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 ((((3 : ℂ) / (2 : ℂ)) ^ (2 : ℕ)) - (2 : ℂ)) ((1 : ℂ) / (4 : ℂ)) (Litex.NativeBridge.denoteSub (_equal_wd_2_0).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_2_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
      let _atomic_wd_1_0 := (_object_w62 (M := M))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2.1 (_equal_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (by norm_num))))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ)))))).trans (by
    let _litex_original := _equal_wd_1_0
    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
    let _wd_1_1 := (_object_w62 (M := M));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (by
      let _atomic_wd_1_0 := (_object_w62 (M := M))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w62 (M := M))).wd.1 ((_object_w62 (M := M))).wd.2.1 ((_object_w62 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_97 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (M.powValue (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from rfl))
  ))).trans _litex_residual)))

theorem h_22822 : (by
  let _chain_wd_22822_0 := (let _object_w67 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w67 (h_96 (M := M)) (by
    let _atomic_wd_1_0 := _object_w67
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_object_w67).wd.1 (_object_w67).wd.2.1 (_object_w67).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) True.intro))
  let _chain_wd_22822_1 := (let _wd_1_0 := (let _wd_2_0 := (_chain_wd_22822_0).val.argument;
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.sub _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((289 : ℂ) / (144 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) ((_atomic_wd_1_0).val.base).wd.1 ((_atomic_wd_1_0).val.base).wd.2.1 ((_atomic_wd_1_0).val.base).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))))).trans (congrArg M.number (by norm_num : (((17 : ℂ) / (12 : ℂ)) ^ (2 : ℕ)) = ((289 : ℂ) / (144 : ℂ))))) (Litex.numberInC (M := M) ((289 : ℂ) / (144 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ))))
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
    let _chain_wd_22822_0 := (let _object_w67 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w67 (h_96 (M := M)) (by
      let _atomic_wd_1_0 := _object_w67
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_object_w67).wd.1 (_object_w67).wd.2.1 (_object_w67).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) True.intro))
    let _chain_wd_22822_1 := (let _wd_1_0 := (let _wd_2_0 := (_chain_wd_22822_0).val.argument;
    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_2_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((289 : ℂ) / (144 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
        let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) ((_atomic_wd_1_0).val.base).wd.1 ((_atomic_wd_1_0).val.base).wd.2.1 ((_atomic_wd_1_0).val.base).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))))).trans (congrArg M.number (by norm_num : (((17 : ℂ) / (12 : ℂ)) ^ (2 : ℕ)) = ((289 : ℂ) / (144 : ℂ))))) (Litex.numberInC (M := M) ((289 : ℂ) / (144 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ))))
    let _chain_wd_22822_2 := _chain_wd_22822_1
    let _chain_wd_22822_3 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (144 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (144 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (144 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (144 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (144 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact (And.intro (let _equal_wd_1_0 := _chain_wd_22822_0;
    let _equal_wd_1_1 := _chain_wd_22822_1;
    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ)))) = (M.subValue (M.powValue (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from by
      have _litex_residual : (M.subValue (M.powValue (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) = (M.subValue (M.powValue (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ)))))).trans (by
      let _litex_original := _equal_wd_1_0
      let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
      let _object_w75 := ((_equal_wd_1_1).val.left).val.base;
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _object_w75 (Litex.formulaFnInFnSet _wd_1_0) (by
        let _atomic_wd_1_0 := _object_w75
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_object_w75).wd.1 (_object_w75).wd.2.1 (_object_w75).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) True.intro))
      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_97 (M := M)) (Litex.sameRefl _litex_original.val.argument)
      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (M.powValue (M.divValue (M.number (17 : ℂ)) (M.number (12 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from rfl))
    ))).trans _litex_residual))) (let _equal_wd_1_0 := _chain_wd_22822_2;
    let _equal_wd_1_1 := _chain_wd_22822_3;
    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((((17 : ℂ) / (12 : ℂ)) ^ (2 : ℕ)) - (2 : ℂ)) ((1 : ℂ) / (144 : ℂ)) (Litex.NativeBridge.denoteSub (_equal_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
      let _atomic_wd_1_0 := ((_equal_wd_1_0).val.left).val.base
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (((_equal_wd_1_0).val.left).val.base).wd.1 (((_equal_wd_1_0).val.left).val.base).wd.2.1 (((_equal_wd_1_0).val.left).val.base).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (144 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (144 : ℂ))) (by norm_num))))))

theorem h_24193 : Litex.Same (let _object_w67 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w67 (h_96 (M := M)) (by
  let _atomic_wd_1_0 := _object_w67
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_object_w67).wd.1 (_object_w67).wd.2.1 (_object_w67).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) True.intro)) (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.sub _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((289 : ℂ) / (144 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) ((_atomic_wd_1_0).val.base).wd.1 ((_atomic_wd_1_0).val.base).wd.2.1 ((_atomic_wd_1_0).val.base).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))))).trans (congrArg M.number (by norm_num : (((17 : ℂ) / (12 : ℂ)) ^ (2 : ℕ)) = ((289 : ℂ) / (144 : ℂ))))) (Litex.numberInC (M := M) ((289 : ℂ) / (144 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ)))) :=
  (And.left (h_22822 (M := M)))

theorem h_24194 : Litex.Same (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.sub _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((289 : ℂ) / (144 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) ((_atomic_wd_1_0).val.base).wd.1 ((_atomic_wd_1_0).val.base).wd.2.1 ((_atomic_wd_1_0).val.base).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))))).trans (congrArg M.number (by norm_num : (((17 : ℂ) / (12 : ℂ)) ^ (2 : ℕ)) = ((289 : ℂ) / (144 : ℂ))))) (Litex.numberInC (M := M) ((289 : ℂ) / (144 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (144 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (144 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (144 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (144 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (144 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) :=
  (And.right (h_22822 (M := M)))

theorem h_24195 : Litex.Same (let _object_w67 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w67 (h_96 (M := M)) (by
  let _atomic_wd_1_0 := _object_w67
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_object_w67).wd.1 (_object_w67).wd.2.1 (_object_w67).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) True.intro)) (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.sub _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((289 : ℂ) / (144 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) ((_atomic_wd_1_0).val.base).wd.1 ((_atomic_wd_1_0).val.base).wd.2.1 ((_atomic_wd_1_0).val.base).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))))).trans (congrArg M.number (by norm_num : (((17 : ℂ) / (12 : ℂ)) ^ (2 : ℕ)) = ((289 : ℂ) / (144 : ℂ))))) (Litex.numberInC (M := M) ((289 : ℂ) / (144 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ)))) :=
  (h_24193 (M := M))

theorem h_24196 : Litex.Same (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.sub _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((289 : ℂ) / (144 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
    let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) ((_atomic_wd_1_0).val.base).wd.1 ((_atomic_wd_1_0).val.base).wd.2.1 ((_atomic_wd_1_0).val.base).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))))).trans (congrArg M.number (by norm_num : (((17 : ℂ) / (12 : ℂ)) ^ (2 : ℕ)) = ((289 : ℂ) / (144 : ℂ))))) (Litex.numberInC (M := M) ((289 : ℂ) / (144 : ℂ))))) (Litex.numberInC (M := M) (2 : ℂ)))) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (144 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (144 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (144 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (144 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (144 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) :=
  (h_24194 (M := M))

theorem h_24197 : Litex.Same (let _object_w67 := (Litex.div (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (Litex.numberInC (M := M) (17 : ℂ)) (Litex.numberInC (M := M) (12 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (12 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w67 (h_96 (M := M)) (by
  let _atomic_wd_1_0 := _object_w67
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((17 : ℂ) / (12 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (17 : ℂ)) (Litex.number (M := M) (12 : ℂ)) (_object_w67).wd.1 (_object_w67).wd.2.1 (_object_w67).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (17 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))) (Litex.NativeBridge.numberInROfEq ((17 : ℂ) / (12 : ℂ)) ((17 : ℝ) / (12 : ℝ)) (by norm_num)))) True.intro)) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (144 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (144 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (144 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (144 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (144 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) :=
  (Eq.trans (h_24193 (M := M)) (h_24194 (M := M)))

theorem h_24199 : ∀ {_Host_i17 : Type v17} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_24204 : Litex.In _value_i17 (Litex.N (M := M))), (by
  let _equal_wd_1_0 := (let _object_w77 := (Litex.add _value_i17 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i17 h_24204) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _object_w77 (h_10028 (M := M)) (by
    let _atomic_wd_1_0 := _object_w77
    exact (Litex.addInN _value_i17 (Litex.number (M := M) (1 : ℂ)) h_24204 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
  let _equal_wd_1_1 := (let _object_w78 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i17 (h_10028 (M := M)) h_24204 True.intro);
  (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _object_w78 (h_7459 (M := M)) (Litex.inRPos_real _object_w78 (by
    let _atomic_wd_1_0 := _object_w78
    exact (by
      let _litex_return_call := _object_w78
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w78)).mp (by
    let _atomic_wd_1_0 := _object_w78
    exact (by
      let _litex_return_call := _object_w78
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))).2))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    intro _Host_i17 _rep_i17 _value_i17 h_24204
    have h_24205 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i17 h_24204)
          )
      )
    have h_24349 : Litex.In _value_i17 (Litex.N (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_24204
          )
      )
    have h_24350 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i17 h_24349)
          )
      )
    let _object_w80 := (Litex.add _value_i17 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i17 h_24349) (Litex.numberInC (M := M) (1 : ℂ)))

    have h_24200 : (by
      let _atomic_wd_1_0 := _object_w80
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w80
              exact (by
                let _litex_zero_bound := _atomic_wd_1_0
                exact Litex.addPositiveRight _litex_zero_bound.val.left _litex_zero_bound.val.right _litex_zero_bound.wd.1 _litex_zero_bound.wd.2 h_24350 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
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
    let _object_w82 := (let _wd_1_0 := _object_w80;
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w80
      exact (Litex.addInC _value_i17 _wd_1_1 (Litex.naturalToComplex _value_i17 h_24349) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))

    have h_24201 : (by
      let _equal_wd_1_0 := _object_w82
      exact Litex.Same _equal_wd_1_0 _value_i17) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w82;
            (show Litex.Same _equal_wd_1_0 _value_i17 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i17 (Litex.naturalToComplex _value_i17 h_24349)) + (1 : ℂ)) - (1 : ℂ)) (Litex.NativeBridge.asComplex _value_i17 (Litex.naturalToComplex _value_i17 h_24349)) (Litex.NativeBridge.denoteSub (_equal_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i17 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i17 h_24349) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i17 (Litex.naturalToComplex _value_i17 h_24349)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i17 (Litex.naturalToComplex _value_i17 h_24349)) (by ring!))))
          )
      )
    let _object_w86 := (let _wd_1_0 := _object_w80;
    (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _wd_1_0 (h_10028 (M := M)) (by
      let _atomic_wd_1_0 := _object_w80
      exact (Litex.addInN _value_i17 (Litex.number (M := M) (1 : ℂ)) h_24349 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))

    let _object_w87 := (let _object_w83 := (let _wd_2_0 := _object_w82;
    (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _wd_2_0 (h_10028 (M := M)) (by
      let _atomic_wd_1_0 := _object_w82
      exact (Litex.inOfSame _value_i17 _atomic_wd_1_0 (Litex.N (M := M)) (Litex.N (M := M)) (h_24201).symm (show @Eq M.Value _ _ from Eq.refl _) h_24349)) True.intro));
    (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _object_w83 (h_7459 (M := M)) (Litex.inRPos_real _object_w83 (by
      let _atomic_wd_1_0 := _object_w83
      exact (by
        let _litex_return_call := _object_w83
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w83)).mp (by
      let _atomic_wd_1_0 := _object_w83
      exact (by
        let _litex_return_call := _object_w83
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))).2))

    have h_24202 : (by
      let _equal_wd_1_0 := _object_w86
      let _equal_wd_1_1 := _object_w87
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w86;
            let _equal_wd_1_1 := _object_w87;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
              let _checked_call := _equal_wd_1_0
              have _checked_case_guard : (by
              let _atomic_wd_1_0 := _object_w80
              exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) := (by
              let _atomic_wd_1_0 := _object_w80
              exact h_24200)
              have _selected_beta := (h_10032 (M := M)) _checked_call.val.argument _checked_call.wd.2.1 _checked_case_guard
              exact _selected_beta.trans (show @Eq M.Value _ _ from Eq.refl _))))
          )
      )
    let _object_w88 := (_object_w87).val.argument

    let _object_w89 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i17 (h_10028 (M := M)) h_24349 True.intro)

    have h_24203 : (by
      let _equal_wd_1_0 := _object_w88
      let _equal_wd_1_1 := _object_w89
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_24201)
          )
      )
    exact (Eq.trans h_24202 (Eq.trans (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_24203) (show @Eq M.Value _ _ from Eq.refl _)))
  )

theorem h_25892 : ∀ {_Host_i19 : Type v19} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_25904 : Litex.In _value_i19 (Litex.RPos (M := M))), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
  let _wd_2_1 := (Litex.powNatReal _value_i19 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i19 h_25904) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
  (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_25904)
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))));
  let _wd_1_1 := (let _object_w94 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i19 (h_7459 (M := M)) (Litex.inRPos_real _value_i19 h_25904) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i19)).mp h_25904).2);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w94 (h_96 (M := M)) (by
    let _atomic_wd_1_0 := _object_w94
    exact (Litex.inRPos_real _object_w94 (Litex.callInOutput _object_w94))) True.intro));
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _litex_power := (_atomic_wd_1_0).val.right
      have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_25904)
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i19 (h_96 (M := M)) (Litex.inRPos_real _value_i19 h_25904) True.intro);
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    intro _Host_i19 _rep_i19 _value_i19 h_25904
    have h_25905 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i19 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i19 h_25904)
          )
      )
    have h_25906 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i19 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i19 h_25905)
          )
      )
    have h_25907 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i19 h_25905) _litex_zero.symm)
          )
      )
    have h_26897 : Litex.In _value_i19 (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_25904
          )
      )
    have h_26898 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i19 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i19 h_26897)
          )
      )
    have h_26899 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i19 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i19 h_26898)
          )
      )
    have h_26900 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i19 h_26898) _litex_zero.symm)
          )
      )
    have h_25893 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i19 :=
      (by
        litex_checked_step =>
          exact (
            h_26898
          )
      )
    have h_25894 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            h_26900
          )
      )
    let _object_i20 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i19 (h_7459 (M := M)) (Litex.inRPos_real _value_i19 h_26897) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i19)).mp h_26897).2)
    have h_27030 : Litex.In _object_i20 (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i19 (h_7459 (M := M)) (Litex.inRPos_real _value_i19 h_26897) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i19)).mp h_26897).2)
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))
          )
      )
    have h_27031 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_i20 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _object_i20 h_27030)
          )
      )
    have h_27032 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_i20 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _object_i20 h_27031)
          )
      )
    have h_27033 : ¬ Litex.Same _object_i20 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _object_i20 h_27031) _litex_zero.symm)
          )
      )
    have h_27034 : Litex.Same _object_i20 _object_i20 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.sameRefl (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i19 (h_7459 (M := M)) (Litex.inRPos_real _value_i19 h_26897) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i19)).mp h_26897).2))
          )
      )
    let _object_w99 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_i20 (h_96 (M := M)) (Litex.inRPos_real _object_i20 h_27030) True.intro)

    let _object_w100 := (let _wd_1_0 := (Litex.powNatReal _object_i20 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i20 h_27030) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.positiveRealToComplex _object_i20 h_27030)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.numberInC (M := M) (2 : ℂ))))

    have h_25895 : (by
      let _equal_wd_1_0 := _object_w99
      let _equal_wd_1_1 := _object_w100
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w99;
            let _equal_wd_1_1 := _object_w100;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _object_i20)) = (M.subValue (M.powValue (Litex.denote _object_i20) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from by
              have _litex_residual : (M.subValue (M.powValue (Litex.denote _object_i20) (M.number (2 : ℂ))) (M.number (2 : ℂ))) = (M.subValue (M.powValue (Litex.denote _object_i20) (M.number (2 : ℂ))) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _object_i20)))).trans (by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
              let _wd_1_1 := _object_i20;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 h_27030) True.intro))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_97 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (M.powValue (Litex.denote _object_i20) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from rfl))
            ))).trans _litex_residual)))
          )
      )
    have h_25896 : (by
      let _chain_wd_25896_0 := (let _wd_1_0 := _object_i20;
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
        let _atomic_wd_1_0 := _object_i20
        exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))) True.intro))
      let _chain_wd_25896_1 := _object_w99
      let _chain_wd_25896_2 := _object_w99
      let _chain_wd_25896_3 := _object_w100
      let _chain_wd_25896_4 := _object_w100
      let _chain_wd_25896_5 := (let _wd_1_0 := (let _wd_2_0 := _object_i20;
      let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
        let _atomic_wd_1_0 := _object_i20
        exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.sub _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
        )) (Litex.numberInC (M := M) (2 : ℂ))))
      exact ((by
        let _equal_wd_1_0 := _chain_wd_25896_0
        let _equal_wd_1_1 := _chain_wd_25896_1
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
        let _equal_wd_1_0 := _chain_wd_25896_2
        let _equal_wd_1_1 := _chain_wd_25896_3
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
        let _equal_wd_1_0 := _chain_wd_25896_4
        let _equal_wd_1_1 := _chain_wd_25896_5
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _chain_wd_25896_0 := (let _wd_1_0 := _object_i20;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
                let _atomic_wd_1_0 := _object_i20
                exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))) True.intro))
              let _chain_wd_25896_1 := _object_w99
              let _chain_wd_25896_2 := _object_w99
              let _chain_wd_25896_3 := _object_w100
              let _chain_wd_25896_4 := _object_w100
              let _chain_wd_25896_5 := (let _wd_1_0 := (let _wd_2_0 := _object_i20;
              let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                let _atomic_wd_1_0 := _object_i20
                exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.sub _wd_1_0 _wd_1_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                )) (Litex.numberInC (M := M) (2 : ℂ))))
              exact (And.intro (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_27034).symm) (And.intro h_25895 (congrArg₂ M.subValue (show (M.powValue (Litex.denote _object_i20) (M.number (2 : ℂ))) = (M.powValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (2 : ℂ))) from (congrArg₂ M.powValue (show (Litex.denote _object_i20) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) from h_27034) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _))))))
          )
      )

    have h_28735 :=
      (And.left h_25896)

    have h_28736 :=
      (And.left (And.right h_25896))

    have h_28737 :=
      (And.right (And.right h_25896))

    have h_28738 :=
      h_28735

    have h_28739 :=
      h_28736

    have h_28740 :=
      h_28737

    have h_28982 : Litex.Same (_object_w100).val.left (let _wd_1_0 := _object_i20;
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _object_i20
      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.subCancelRightRight (_object_w100).val.left (let _wd_1_0 := _object_i20;
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_i20
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.number (M := M) (2 : ℂ)) (by
              let _atomic_wd_1_0 := (_object_w100).val.left
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.positiveRealToComplex _object_i20 h_27030)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              )) (by
              let _atomic_wd_1_0 := (let _wd_1_0 := _object_i20;
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                let _atomic_wd_2_0 := _object_i20
                exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.inOfSame _object_i20 _atomic_wd_2_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              )) (Litex.numberInC (M := M) (2 : ℂ)) h_28740)
          )
      )

    have h_28983 :=
      (Eq.trans h_28735 h_28736)

    have h_28984 :=
      (Eq.trans (Eq.trans h_28735 h_28736) h_28737)

    have h_28985 :=
      (Eq.trans h_28736 h_28737)
    let _object_w101 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i19 (h_96 (M := M)) (Litex.inRPos_real _value_i19 h_26897) True.intro)

    let _object_w102 := (let _wd_1_0 := (Litex.powNatReal _value_i19 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i19 h_26897) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_26897)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.numberInC (M := M) (2 : ℂ))))

    have h_25897 : (by
      let _equal_wd_1_0 := _object_w101
      let _equal_wd_1_1 := _object_w102
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w101;
            let _equal_wd_1_1 := _object_w102;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i19)) = (M.subValue (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from by
              have _litex_residual : (M.subValue (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ))) (M.number (2 : ℂ))) = (M.subValue (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ))) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i19)))).trans (by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
              let _wd_1_1 := _value_i19;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 h_26897) True.intro))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_97 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.subValue (M.powValue _raw_i2 (M.number (2 : ℂ))) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w103 := (let _wd_1_0 := (let _wd_2_0 := _value_i19;
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_26897) h_26900);
    (Litex.add _wd_2_0 _wd_2_1 (Litex.positiveRealToComplex _wd_2_0 h_26897) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_26897) (_atomic_wd_1_0).wd.2.2))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.addInC _value_i19 (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex _value_i19 h_26897) (Litex.divInC _wd_1_1 _value_i19 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i19 h_26897) ((_atomic_wd_1_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

    have h_25898 : (by
      let _equal_wd_1_0 := _object_i20
      let _equal_wd_1_1 := _object_w103
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) = (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) from by
              have _litex_residual : (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) = (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)))).trans (by
              let _litex_original := _object_i20
              let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
              let _wd_1_1 := _value_i19;
              (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 h_26897) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp h_26897).2))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_7460 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) from rfl))
            ))).trans _litex_residual)
          )
      )
    let _object_w104 := (let _wd_1_0 := (let _wd_2_0 := _object_i20;
    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _object_i20
      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.numberInC (M := M) (2 : ℂ))))

    let _object_w105 := (let _wd_1_0 := (let _wd_2_0 := _object_w103;
    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _object_w103
      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) ((h_27034).trans h_25898) (show @Eq M.Value _ _ from Eq.refl _) h_27030))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) ((h_27034).trans h_25898) (show @Eq M.Value _ _ from Eq.refl _) h_27030))
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.numberInC (M := M) (2 : ℂ))))

    have h_25899 : (by
      let _equal_wd_1_0 := _object_w104
      let _equal_wd_1_1 := _object_w105
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ M.subValue (show (M.powValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) (M.number (2 : ℂ))) = (M.powValue (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from (congrArg₂ M.powValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19)) = (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) from h_25898) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))
          )
      )

    have h_34395 : Litex.Same (_object_w104).val.left (_object_w105).val.left :=
      (by
        litex_checked_step =>
          exact (
            (Litex.subCancelRightRight (_object_w104).val.left (_object_w105).val.left (Litex.number (M := M) (2 : ℂ)) (by
              let _atomic_wd_1_0 := (_object_w104).val.left
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              )) (by
              let _atomic_wd_1_0 := (_object_w105).val.left
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.positiveRealToComplex (_atomic_wd_1_0).val.base (Litex.inOfSame _object_i20 (_atomic_wd_1_0).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) ((h_27034).trans h_25898) (show @Eq M.Value _ _ from Eq.refl _) h_27030))
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              )) (Litex.numberInC (M := M) (2 : ℂ)) h_25899)
          )
      )
    have h_25900 : (by
      let _chain_wd_25900_0 := (let _wd_1_0 := _object_i20;
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
        let _atomic_wd_1_0 := _object_i20
        exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))) True.intro))
      let _chain_wd_25900_1 := _object_w104
      let _chain_wd_25900_2 := _object_w104
      let _chain_wd_25900_3 := _object_w105
      exact ((by
        let _equal_wd_1_0 := _chain_wd_25900_0
        let _equal_wd_1_1 := _chain_wd_25900_1
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
        let _equal_wd_1_0 := _chain_wd_25900_2
        let _equal_wd_1_1 := _chain_wd_25900_3
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _chain_wd_25900_0 := (let _wd_1_0 := _object_i20;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
                let _atomic_wd_1_0 := _object_i20
                exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))) True.intro))
              let _chain_wd_25900_1 := _object_w104
              let _chain_wd_25900_2 := _object_w104
              let _chain_wd_25900_3 := _object_w105
              exact (And.intro h_28984 h_25899))
          )
      )

    have h_34438 :=
      (And.left h_25900)

    have h_34439 :=
      (And.right h_25900)

    have h_34440 :=
      h_34438

    have h_34441 :=
      h_34439

    have h_34442 :=
      (Eq.trans h_34438 h_34439)
    let _object_w106 := (let _wd_1_0 := _object_w101;
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _object_w101
      exact (by
        let _litex_return_call := _object_w101
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

    let _object_w107 := (let _wd_1_0 := _object_w102;
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _object_w102
      exact (Litex.subInR (_object_w102).val.left _wd_1_1 (by
        let _litex_power := (_object_w102).val.left
        have _elaborated_power_base := (Litex.inRPos_real _value_i19 h_26897)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInR _litex_power _recorded_power_base
      ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

    have h_25901 : (by
      let _equal_wd_1_0 := _object_w106
      let _equal_wd_1_1 := _object_w107
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ M.powValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i19)) = (M.subValue (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from h_25897) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))
          )
      )
    let _object_w108 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_2_1 := (_object_w102).val.left;
    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_26897)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))));
    let _wd_1_1 := _object_w105;
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _litex_power := (_atomic_wd_1_0).val.right
        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_26897)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))) (by
      let _atomic_wd_1_0 := _object_w105
      exact (Litex.subInC (_object_w105).val.left (Litex.number (M := M) (2 : ℂ)) (by
        let _litex_power := (_object_w105).val.left
        have _elaborated_power_base := (Litex.positiveRealToComplex ((_object_w105).val.left).val.base (Litex.inOfSame _object_i20 ((_object_w105).val.left).val.base (Litex.RPos (M := M)) (Litex.RPos (M := M)) ((h_27034).trans h_25898) (show @Eq M.Value _ _ from Eq.refl _) h_27030))
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ) (Litex.numberInC (M := M) (2 : ℂ))))))

    have h_25902 : (by
      let _equal_wd_1_0 := _object_w108
      let _equal_wd_1_1 := _object_w107
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w108;
            let _equal_wd_1_1 := _object_w107;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((4 : ℂ) * ((Litex.NativeBridge.asComplex _value_i19 (Litex.positiveRealToComplex _value_i19 h_26897)) ^ (2 : ℕ))) * (((((Litex.NativeBridge.asComplex _value_i19 (Litex.positiveRealToComplex _value_i19 h_26897)) + ((2 : ℂ) / (Litex.NativeBridge.asComplex _value_i19 (Litex.positiveRealToComplex _value_i19 h_26897)))) / (2 : ℂ)) ^ (2 : ℕ)) - (2 : ℂ))) ((((Litex.NativeBridge.asComplex _value_i19 (Litex.positiveRealToComplex _value_i19 h_26897)) ^ (2 : ℕ)) - (2 : ℂ)) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) ((_equal_wd_1_0).val.left).val.right ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denotePowNatReal _value_i19 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i19 h_26897) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i19 (Litex.positiveRealToComplex _value_i19 h_26897)))) (Litex.NativeBridge.denoteSub (_object_w105).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w105).wd.1 (_object_w105).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_object_w105).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_w103
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) ((h_27034).trans h_25898) (show @Eq M.Value _ _ from Eq.refl _) h_27030))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (_object_w103).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w103).wd.1 (_object_w103).wd.2.1 (_object_w103).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i19 ((_object_w103).val.left).val.right ((_object_w103).val.left).wd.1 ((_object_w103).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i19 (Litex.positiveRealToComplex _value_i19 h_26897)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) _value_i19 (((_object_w103).val.left).val.right).wd.1 (((_object_w103).val.left).val.right).wd.2.1 (((_object_w103).val.left).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i19 (Litex.positiveRealToComplex _value_i19 h_26897)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denotePowNatReal (_object_w107).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_w102
              exact (Litex.subInR (_object_w102).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w102).val.left
                have _elaborated_power_base := (Litex.inRPos_real _value_i19 h_26897)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInR _litex_power _recorded_power_base
              ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub (_object_w102).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w102).wd.1 (_object_w102).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal _value_i19 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i19 h_26897) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i19 (Litex.positiveRealToComplex _value_i19 h_26897))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (by
              have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i19 (Litex.positiveRealToComplex _value_i19 h_26897)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i19 (Litex.NativeBridge.asComplex _value_i19 (Litex.positiveRealToComplex _value_i19 h_26897)) (Litex.NativeBridge.asComplex_spec _value_i19 (Litex.positiveRealToComplex _value_i19 h_26897)) h_26900
              have _litex_nz_1 : ((2 : ℂ) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
              litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | exact _litex_nz_1 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
            ))))
          )
      )
    have h_25903 : (by
      let _chain_wd_25903_0 := (let _wd_1_0 := (_object_w108).val.left;
      let _wd_1_1 := (let _wd_2_0 := _object_i20;
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_96 (M := M)) (by
        let _atomic_wd_1_0 := _object_i20
        exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))) True.intro));
      (Litex.mul _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
          let _litex_power := (_atomic_wd_1_0).val.right
          have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_26897)
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
        ))) (by
        let _atomic_wd_1_0 := _wd_1_1
        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
      let _chain_wd_25903_1 := _object_w108
      let _chain_wd_25903_2 := _object_w108
      let _chain_wd_25903_3 := _object_w107
      let _chain_wd_25903_4 := _object_w107
      let _chain_wd_25903_5 := _object_w106
      exact ((by
        let _equal_wd_1_0 := _chain_wd_25903_0
        let _equal_wd_1_1 := _chain_wd_25903_1
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
        let _equal_wd_1_0 := _chain_wd_25903_2
        let _equal_wd_1_1 := _chain_wd_25903_3
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
        let _equal_wd_1_0 := _chain_wd_25903_4
        let _equal_wd_1_1 := _chain_wd_25903_5
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _chain_wd_25903_0 := (let _wd_1_0 := (_object_w108).val.left;
              let _wd_1_1 := (let _wd_2_0 := _object_i20;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_96 (M := M)) (by
                let _atomic_wd_1_0 := _object_i20
                exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i20 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_27034 (show @Eq M.Value _ _ from Eq.refl _) h_27030))) True.intro));
              (Litex.mul _wd_1_0 _wd_1_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                  let _litex_power := (_atomic_wd_1_0).val.right
                  have _elaborated_power_base := (Litex.positiveRealToComplex _value_i19 h_26897)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                ))) (by
                let _atomic_wd_1_0 := _wd_1_1
                exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
              let _chain_wd_25903_1 := _object_w108
              let _chain_wd_25903_2 := _object_w108
              let _chain_wd_25903_3 := _object_w107
              let _chain_wd_25903_4 := _object_w107
              let _chain_wd_25903_5 := _object_w106
              exact (And.intro (congrArg₂ M.mulValue (show (M.mulValue (M.number (4 : ℂ)) (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ)))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (Litex.denote _value_i19) (M.number (2 : ℂ)))) from (show @Eq M.Value _ _ from Eq.refl _)) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i19))) = (M.subValue (M.powValue (M.divValue (M.addValue (Litex.denote _value_i19) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i19))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) (M.number (2 : ℂ))) from h_34442)) (And.intro h_25902 (h_25901).symm)))
          )
      )

    have h_43922 :=
      (And.left h_25903)

    have h_43923 :=
      (And.left (And.right h_25903))

    have h_43924 :=
      (And.right (And.right h_25903))

    have h_43925 :=
      h_43922

    have h_43926 :=
      h_43923

    have h_43927 :=
      h_43924

    have h_49504 :=
      (Eq.trans h_43922 h_43923)

    have h_49505 :=
      (Eq.trans (Eq.trans h_43922 h_43923) h_43924)

    have h_49506 :=
      (Eq.trans h_43923 h_43924)
    exact h_49505
  )

theorem h_51179 : ∀ {_Host_i22 : Type v22} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (h_51193 : Litex.In _value_i22 (Litex.RPos (M := M))), (by
  let _atomic_wd_1_0 := (let _object_w113 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_51193) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_51193).2);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w113 (h_96 (M := M)) (by
    let _atomic_wd_2_0 := _object_w113
    exact (Litex.inRPos_real _object_w113 (Litex.callInOutput _object_w113))) True.intro))
  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
  (by
    intro _Host_i22 _rep_i22 _value_i22 h_51193
    have h_51194 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i22 h_51193)
          )
      )
    have h_51195 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i22 h_51194)
          )
      )
    have h_51196 : ¬ Litex.Same _value_i22 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i22 h_51194) _litex_zero.symm)
          )
      )
    have h_51589 : Litex.In _value_i22 (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_51193
          )
      )
    have h_51590 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i22 h_51589)
          )
      )
    have h_51591 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i22 h_51590)
          )
      )
    have h_51592 : ¬ Litex.Same _value_i22 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i22 h_51590) _litex_zero.symm)
          )
      )
    have h_51594 : Litex.Same (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_51589) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))));
    let _wd_1_1 := (let _object_w118 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_51589) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_51589).2);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w118 (h_96 (M := M)) (by
      let _atomic_wd_1_0 := _object_w118
      exact (Litex.inRPos_real _object_w118 (Litex.callInOutput _object_w118))) True.intro));
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _litex_power := (_atomic_wd_1_0).val.right
        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))))) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_51589) True.intro);
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
              have h_51593 : Litex.In _value_i22 (Litex.RPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      h_51589
                    )
                )
              have h_51599 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inRPos_positive _value_i22 h_51593)
                    )
                )
              have h_51600 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i22 h_51599)
                    )
                )
              have h_51601 : ¬ Litex.Same _value_i22 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i22 h_51599) _litex_zero.symm)
                    )
                )
              exact ((h_25892 (M := M)) _value_i22 h_51593)
            )
          )
      )
    have h_51180 : (by
      let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
      let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_51589) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
      (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _atomic_wd_1_0 := _wd_2_1
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
        ))));
      let _wd_1_1 := (let _object_w118 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_51589) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_51589).2);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w118 (h_96 (M := M)) (by
        let _atomic_wd_1_0 := _object_w118
        exact (Litex.inRPos_real _object_w118 (Litex.callInOutput _object_w118))) True.intro));
      (Litex.mul _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
          let _litex_power := (_atomic_wd_1_0).val.right
          have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
        ))) (by
        let _atomic_wd_1_0 := _wd_1_1
        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
      let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_51589) True.intro);
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
            h_51594
          )
      )
    let _object_w122 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_51589) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))

    have h_51181 : (by
      let _atomic_wd_1_0 := _object_w122
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w122
              exact (by
                let _atomic_wd_2_1 := _atomic_wd_1_0
                exact (Litex.powStructuralPositiveOfEven _atomic_wd_2_1 (Litex.inRPos_real _value_i22 h_51589) (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num) (by norm_num) h_51592)))
          )
      )
    let _object_w124 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_1_1 := _object_w122;
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _object_w122
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))))

    have h_51182 : (by
      let _atomic_wd_1_0 := _object_w124
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w124
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
                let _atomic_wd_2_1 := _object_w122
                exact h_51181)
              ))
          )
      )
    have h_51183 : (by
      let _atomic_wd_1_0 := _object_w124
      exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w124
              exact (fun _litex_equal => (Litex.ltNotSame (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0 h_51182) _litex_equal.symm))
          )
      )
    have h_51184 : (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_51589) True.intro);
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
              let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_51589) True.intro);
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (by
                  let _litex_return_call := _atomic_wd_1_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              exact (by
                let _atomic_wd_2_1 := _atomic_wd_1_0
                exact (Litex.powStructuralNonnegativeOfEven _atomic_wd_2_1 (by
                  let _atomic_wd_3_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_51589) True.intro)
                  exact (by
                    let _litex_return_call := _atomic_wd_3_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num))))
          )
      )
    have h_51185 : (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
      let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_51589) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
      (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _atomic_wd_1_0 := _wd_2_1
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
        ))));
      let _wd_1_1 := (let _object_w118 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_51589) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_51589).2);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w118 (h_96 (M := M)) (by
        let _atomic_wd_1_0 := _object_w118
        exact (Litex.inRPos_real _object_w118 (Litex.callInOutput _object_w118))) True.intro));
      (Litex.mul _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
          let _litex_power := (_atomic_wd_1_0).val.right
          have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
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
              let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_51589) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
              (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _atomic_wd_1_0 := _wd_2_1
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                ))));
              let _wd_1_1 := (let _object_w118 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_51589) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_51589).2);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w118 (h_96 (M := M)) (by
                let _atomic_wd_1_0 := _object_w118
                exact (Litex.inRPos_real _object_w118 (Litex.callInOutput _object_w118))) True.intro));
              (Litex.mul _wd_1_0 _wd_1_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                  let _litex_power := (_atomic_wd_1_0).val.right
                  have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                ))) (by
                let _atomic_wd_1_0 := _wd_1_1
                exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
              exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_51589) True.intro);
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (by
                  let _litex_return_call := _atomic_wd_1_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) _atomic_wd_1_0 (show @Eq M.Value _ _ from Eq.refl _) (h_51594).symm h_51184))
          )
      )
    let _object_w148 := (let _object_w147 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_51589) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_51589).2);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w147 (h_96 (M := M)) (by
      let _atomic_wd_1_0 := _object_w147
      exact (Litex.inRPos_real _object_w147 (Litex.callInOutput _object_w147))) True.intro))

    have h_51186 : (by
      let _atomic_wd_1_0 := _object_w148
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w148
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
          )
      )
    have h_51187 : (by
      let _atomic_wd_1_0 := _object_w122
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w122
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.inRPos_real _value_i22 h_51589)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInR _litex_power _recorded_power_base
              ))
          )
      )
    have h_51188 : (by
      let _atomic_wd_1_0 := _object_w124
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w124
              exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) (_object_w124).val.right (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) h_51187))
          )
      )
    have h_51189 : (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
      let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_51589) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
      (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _atomic_wd_1_0 := _wd_2_1
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
        ))));
      let _wd_1_1 := (let _object_w118 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_51589) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_51589).2);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w118 (h_96 (M := M)) (by
        let _atomic_wd_1_0 := _object_w118
        exact (Litex.inRPos_real _object_w118 (Litex.callInOutput _object_w118))) True.intro));
      (Litex.mul _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
          let _litex_power := (_atomic_wd_1_0).val.right
          have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
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
              let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_51589) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
              (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _atomic_wd_1_0 := _wd_2_1
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                ))));
              let _wd_1_1 := (let _object_w118 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_51589) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_51589).2);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w118 (h_96 (M := M)) (by
                let _atomic_wd_1_0 := _object_w118
                exact (Litex.inRPos_real _object_w118 (Litex.callInOutput _object_w118))) True.intro));
              (Litex.mul _wd_1_0 _wd_1_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                  let _litex_power := (_atomic_wd_1_0).val.right
                  have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                ))) (by
                let _atomic_wd_1_0 := _wd_1_1
                exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
              exact (Litex.mulInR _object_w124 _object_w148 h_51188 h_51186))
          )
      )
    let _object_w150 := (let _wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_2_1 := (Litex.powNatReal _value_i22 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i22 h_51589) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))));
    let _wd_1_1 := (let _object_w118 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i22 (h_7459 (M := M)) (Litex.inRPos_real _value_i22 h_51589) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i22)).mp h_51589).2);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w118 (h_96 (M := M)) (by
      let _atomic_wd_1_0 := _object_w118
      exact (Litex.inRPos_real _object_w118 (Litex.callInOutput _object_w118))) True.intro));
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _litex_power := (_atomic_wd_1_0).val.right
        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i22 h_51589)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))));
    let _wd_1_1 := _object_w124;
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (M.real_subset_complex _ h_51189)) (by
      let _atomic_wd_1_0 := _object_w124
      exact (M.real_subset_complex _ h_51188)) (by
      let _atomic_wd_1_0 := _object_w124
      exact h_51183)))

    have h_51190 : (by
      let _atomic_wd_1_0 := _object_w150
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w150
              exact (Litex.divInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right h_51189 h_51188 (_atomic_wd_1_0).wd.2.2))
          )
      )
    have h_51191 : (by
      let _atomic_wd_1_0 := _object_w150
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w150
              exact (Litex.divStructuralNonnegative _atomic_wd_1_0 (by
                let _atomic_wd_2_1 := _object_w124
                exact h_51182) (by
                let _atomic_wd_2_1 := (_object_w150).val.left
                exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_96 (M := M)) (Litex.inRPos_real _value_i22 h_51589) True.intro);
                let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (by
                    let _litex_return_call := _atomic_wd_1_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (h_51594).symm h_51184))))
          )
      )
    have h_51192 : (by
      let _chain_wd_51192_0 := _object_w148
      let _chain_wd_51192_1 := _object_w150
      exact ((by
        let _equal_wd_1_0 := _chain_wd_51192_0
        let _equal_wd_1_1 := _chain_wd_51192_1
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
        let _atomic_wd_1_0 := _object_w150
        exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _chain_wd_51192_0 := _object_w148
              let _chain_wd_51192_1 := _object_w150
              exact (And.intro (let _equal_wd_1_0 := _chain_wd_51192_0;
              let _equal_wd_1_1 := _chain_wd_51192_1;
              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                let _quotient := _equal_wd_1_1
                let _product := (_object_w150).val.left
                have _child : (by
                  let _equal_wd_2_0 := (_object_w150).val.left
                  let _equal_wd_2_1 := _equal_wd_2_0
                  exact Litex.Same _equal_wd_2_1 _equal_wd_2_1) := (show @Eq M.Value _ _ from Eq.refl _)
                have _conversion := Litex.sameDivIffSameMul _quotient.val.left _quotient.val.right _product.val.right _quotient.wd.1 _quotient.wd.2.1 _product.wd.2 _quotient.wd.2.2
                exact ((_conversion.mpr (_child.trans (Litex.sameMulComm _product.val.left _product.val.right _product.wd.1 _product.wd.2))).symm)))) (by
                let _atomic_wd_1_0 := _object_w150
                exact h_51191)))
          )
      )

    have h_71270 :=
      (And.left h_51192)

    have h_71271 :=
      (And.right h_51192)

    have h_71272 :=
      h_71270

    have h_71273 :=
      h_71271

    have h_71541 :=
      (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w150 _object_w148 (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (Eq.symm h_71270) h_71271)
    exact (by
      let _atomic_wd_1_0 := _object_w148
      exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w150 _atomic_wd_1_0 (show @Eq M.Value _ _ from Eq.refl _) (h_71270).symm h_51191))
  )

theorem h_71947 : ∀ {_Host_i24 : Type v24} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (h_71956 : Litex.In _value_i24 (Litex.RPos (M := M))), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
  let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_71956) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
  (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71956)
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
    ))));
  let _wd_1_1 := (let _wd_2_0 := (let _object_w155 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_71956) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_71956).2);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w155 (h_96 (M := M)) (by
    let _atomic_wd_1_0 := _object_w155
    exact (Litex.inRPos_real _object_w155 (Litex.callInOutput _object_w155))) True.intro));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _litex_power := (_atomic_wd_1_0).val.right
      have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_71956)
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
  let _equal_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_71956) True.intro);
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
    intro _Host_i24 _rep_i24 _value_i24 h_71956
    have h_71957 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i24 h_71956)
          )
      )
    have h_71958 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i24 h_71957)
          )
      )
    have h_71959 : ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i24 h_71957) _litex_zero.symm)
          )
      )
    have h_73562 : Litex.In _value_i24 (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_71956
          )
      )
    have h_73563 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i24 h_73562)
          )
      )
    have h_73564 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i24 h_73563)
          )
      )
    have h_73565 : ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i24 h_73563) _litex_zero.symm)
          )
      )
    have h_73567 : Litex.Same (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_73562) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_73562)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))));
    let _wd_1_1 := (let _object_w162 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w162 (h_96 (M := M)) (by
      let _atomic_wd_1_0 := _object_w162
      exact (Litex.inRPos_real _object_w162 (Litex.callInOutput _object_w162))) True.intro));
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _litex_power := (_atomic_wd_1_0).val.right
        have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_73562)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))))) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_73562) True.intro);
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
              have h_73566 : Litex.In _value_i24 (Litex.RPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      h_73562
                    )
                )
              have h_73572 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inRPos_positive _value_i24 h_73566)
                    )
                )
              have h_73573 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i24 h_73572)
                    )
                )
              have h_73574 : ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i24 h_73572) _litex_zero.symm)
                    )
                )
              exact ((h_25892 (M := M)) _value_i24 h_73566)
            )
          )
      )
    have h_71948 : (by
      let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
      let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_73562) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
      (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _atomic_wd_1_0 := _wd_2_1
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_73562)
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
        ))));
      let _wd_1_1 := (let _object_w162 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w162 (h_96 (M := M)) (by
        let _atomic_wd_1_0 := _object_w162
        exact (Litex.inRPos_real _object_w162 (Litex.callInOutput _object_w162))) True.intro));
      (Litex.mul _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
          let _litex_power := (_atomic_wd_1_0).val.right
          have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_73562)
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
        ))) (by
        let _atomic_wd_1_0 := _wd_1_1
        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
      let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_73562) True.intro);
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
            h_73567
          )
      )
    have h_80263 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (let _object_w169 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w169 (h_96 (M := M)) (by
      let _atomic_wd_1_0 := _object_w169
      exact (Litex.inRPos_real _object_w169 (Litex.callInOutput _object_w169))) True.intro)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_80262 : Litex.In _value_i24 (Litex.RPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      h_73562
                    )
                )
              have h_80268 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inRPos_positive _value_i24 h_80262)
                    )
                )
              have h_80269 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i24 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i24 h_80268)
                    )
                )
              have h_80270 : ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i24 h_80268) _litex_zero.symm)
                    )
                )
              exact ((h_51179 (M := M)) _value_i24 h_80262)
            )
          )
      )
    have h_71949 : (by
      let _atomic_wd_1_0 := (let _object_w169 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w169 (h_96 (M := M)) (by
        let _atomic_wd_1_0 := _object_w169
        exact (Litex.inRPos_real _object_w169 (Litex.callInOutput _object_w169))) True.intro))
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := (let _object_w169 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w169 (h_96 (M := M)) (by
                let _atomic_wd_1_0 := _object_w169
                exact (Litex.inRPos_real _object_w169 (Litex.callInOutput _object_w169))) True.intro))
              exact h_80263)
          )
      )
    have h_71950 : (by
      let _atomic_wd_1_0 := (let _object_w169 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w169 (h_96 (M := M)) (by
        let _atomic_wd_1_0 := _object_w169
        exact (Litex.inRPos_real _object_w169 (Litex.callInOutput _object_w169))) True.intro))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := (let _object_w169 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w169 (h_96 (M := M)) (by
                let _atomic_wd_1_0 := _object_w169
                exact (Litex.inRPos_real _object_w169 (Litex.callInOutput _object_w169))) True.intro))
              exact (by
                let _litex_return_call := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2) (h_96 (M := M)) (by
                let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2)
                exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2)))) True.intro)
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
          )
      )
    have h_71951 : (by
      let _atomic_wd_1_1 := (let _object_w169 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w169 (h_96 (M := M)) (by
        let _atomic_wd_1_0 := _object_w169
        exact (Litex.inRPos_real _object_w169 (Litex.callInOutput _object_w169))) True.intro))
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_1 := (let _object_w169 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w169 (h_96 (M := M)) (by
                let _atomic_wd_1_0 := _object_w169
                exact (Litex.inRPos_real _object_w169 (Litex.callInOutput _object_w169))) True.intro))
              exact h_80263)
          )
      )
    let _object_w173 := (let _wd_1_0 := (let _object_w169 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w169 (h_96 (M := M)) (by
      let _atomic_wd_1_0 := _object_w169
      exact (Litex.inRPos_real _object_w169 (Litex.callInOutput _object_w169))) True.intro));
    (Litex.abs _wd_1_0 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact h_71950)))

    have h_71952 : (by
      let _equal_wd_1_0 := _object_w173
      let _equal_wd_1_1 := (_equal_wd_1_0).val.arg
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w173;
            let _equal_wd_1_1 := (_equal_wd_1_0).val.arg;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
              let _litex_abs := _equal_wd_1_0
              exact (Litex.absOfNonnegative _litex_abs.val.arg _litex_abs.wd (by
              let _atomic_wd_1_1 := _equal_wd_1_1
              exact h_71951))
            )))
          )
      )
    let _object_w174 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_73562) True.intro)

    have h_71953 : (by
      let _atomic_wd_1_0 := _object_w174
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w174
              exact (by
                let _litex_return_call := _atomic_wd_1_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
          )
      )
    let _object_w175 := (let _wd_1_0 := (let _wd_2_0 := _object_w174;
    (Litex.abs _wd_2_0 (by
      let _atomic_wd_1_0 := _object_w174
      exact h_71953)));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (by
        let _litex_abs := _atomic_wd_1_0
        exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
      )) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

    have h_71954 : (by
      let _equal_wd_1_0 := _object_w175
      let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_73562) True.intro);
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
            (let _equal_wd_1_0 := _object_w175;
            let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_73562) True.intro);
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
    have h_71955 : (by
      let _chain_wd_71955_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
      let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_73562) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
      (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _atomic_wd_1_0 := _wd_2_1
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_73562)
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
        ))));
      let _wd_1_1 := _object_w173;
      (Litex.mul _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
          let _litex_power := (_atomic_wd_1_0).val.right
          have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_73562)
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
        ))) (by
        let _atomic_wd_1_0 := _object_w173
        exact (M.real_subset_complex _ (Litex.inOfSame (_object_w173).val.arg _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_71952).symm (show @Eq M.Value _ _ from Eq.refl _) h_71950)))))
      let _chain_wd_71955_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
      let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_73562) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
      (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _atomic_wd_1_0 := _wd_2_1
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_73562)
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
        ))));
      let _wd_1_1 := (let _object_w162 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2);
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w162 (h_96 (M := M)) (by
        let _atomic_wd_1_0 := _object_w162
        exact (Litex.inRPos_real _object_w162 (Litex.callInOutput _object_w162))) True.intro));
      (Litex.mul _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
          let _litex_power := (_atomic_wd_1_0).val.right
          have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_73562)
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
        ))) (by
        let _atomic_wd_1_0 := _wd_1_1
        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
      let _chain_wd_71955_2 := _chain_wd_71955_1
      let _chain_wd_71955_3 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_73562) True.intro);
      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (by
          let _litex_return_call := _atomic_wd_1_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
      let _chain_wd_71955_4 := _chain_wd_71955_3
      let _chain_wd_71955_5 := _object_w175
      exact ((by
        let _equal_wd_1_0 := _chain_wd_71955_0
        let _equal_wd_1_1 := _chain_wd_71955_1
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
        let _equal_wd_1_0 := _chain_wd_71955_2
        let _equal_wd_1_1 := _chain_wd_71955_3
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
        let _equal_wd_1_0 := _chain_wd_71955_4
        let _equal_wd_1_1 := _chain_wd_71955_5
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _chain_wd_71955_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
              let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_73562) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
              (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _atomic_wd_1_0 := _wd_2_1
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_73562)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                ))));
              let _wd_1_1 := _object_w173;
              (Litex.mul _wd_1_0 _wd_1_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                  let _litex_power := (_atomic_wd_1_0).val.right
                  have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_73562)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                ))) (by
                let _atomic_wd_1_0 := _object_w173
                exact (M.real_subset_complex _ (Litex.inOfSame (_object_w173).val.arg _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_71952).symm (show @Eq M.Value _ _ from Eq.refl _) h_71950)))))
              let _chain_wd_71955_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
              let _wd_2_1 := (Litex.powNatReal _value_i24 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _value_i24 h_73562) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
              (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _atomic_wd_1_0 := _wd_2_1
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_73562)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                ))));
              let _wd_1_1 := (let _object_w162 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i24 (h_7459 (M := M)) (Litex.inRPos_real _value_i24 h_73562) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i24)).mp h_73562).2);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w162 (h_96 (M := M)) (by
                let _atomic_wd_1_0 := _object_w162
                exact (Litex.inRPos_real _object_w162 (Litex.callInOutput _object_w162))) True.intro));
              (Litex.mul _wd_1_0 _wd_1_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (by
                  let _litex_power := (_atomic_wd_1_0).val.right
                  have _elaborated_power_base := (Litex.positiveRealToComplex _value_i24 h_73562)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                ))) (by
                let _atomic_wd_1_0 := _wd_1_1
                exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
              let _chain_wd_71955_2 := _chain_wd_71955_1
              let _chain_wd_71955_3 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i24 (h_96 (M := M)) (Litex.inRPos_real _value_i24 h_73562) True.intro);
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (by
                  let _litex_return_call := _atomic_wd_1_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              let _chain_wd_71955_4 := _chain_wd_71955_3
              let _chain_wd_71955_5 := _object_w175
              exact (And.intro (congrArg₂ M.mulValue (show (M.mulValue (M.number (4 : ℂ)) (M.powValue (Litex.denote _value_i24) (M.number (2 : ℂ)))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (Litex.denote _value_i24) (M.number (2 : ℂ)))) from (show @Eq M.Value _ _ from Eq.refl _)) (show (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i24)))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i24))) from h_71952)) (And.intro h_73567 (h_71954).symm)))
          )
      )

    have h_85140 :=
      (And.left h_71955)

    have h_85141 :=
      (And.left (And.right h_71955))

    have h_85142 :=
      (And.right (And.right h_71955))

    have h_85143 :=
      h_85140

    have h_85144 :=
      h_85141

    have h_85145 :=
      h_85142

    have h_88602 :=
      (Eq.trans h_85140 h_85141)

    have h_88603 :=
      (Eq.trans (Eq.trans h_85140 h_85141) h_85142)

    have h_88604 :=
      (Eq.trans h_85141 h_85142)
    exact h_88603
  )

theorem h_90742 : ∀ {_Host_i26 : Type v26} [_rep_i26 : Litex.Representation M _Host_i26] (_value_i26 : Litex.Obj (M := M) _Host_i26) (h_90755 : Litex.In _value_i26 (Litex.RPos (M := M))), (by
  let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i26 (h_7459 (M := M)) (Litex.inRPos_real _value_i26 h_90755) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i26)).mp h_90755).2)
  exact Litex.Lt (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0) :=
  (by
    intro _Host_i26 _rep_i26 _value_i26 h_90755
    have h_90756 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i26 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i26 h_90755)
          )
      )
    have h_90757 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i26 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i26 h_90756)
          )
      )
    have h_90758 : ¬ Litex.Same _value_i26 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i26 h_90756) _litex_zero.symm)
          )
      )
    have h_90904 : Litex.In _value_i26 (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_90755
          )
      )
    have h_90905 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i26 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i26 h_90904)
          )
      )
    have h_90906 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i26 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i26 h_90905)
          )
      )
    have h_90907 : ¬ Litex.Same _value_i26 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i26 h_90905) _litex_zero.symm)
          )
      )
    have h_90743 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i26 :=
      (by
        litex_checked_step =>
          exact (
            h_90905
          )
      )
    have h_90744 : ¬ Litex.Same _value_i26 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            h_90907
          )
      )
    let _object_w184 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) _value_i26 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i26 h_90904))

    have h_90745 : (by
      let _atomic_wd_1_0 := _object_w184
      exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w184
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904))) (0 : ℂ) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i26 (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (mul_ne_zero (Litex.NativeBridge.nativeNonzeroOfDenote (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (Litex.NativeBridge.nativeNonzeroOfDenote _value_i26 (Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904)) (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904)) h_90907))))
          )
      )
    let _object_w185 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _value_i26 (h_7459 (M := M)) (Litex.inRPos_real _value_i26 h_90904) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i26)).mp h_90904).2)

    let _object_w186 := (let _wd_1_0 := (let _wd_2_0 := _value_i26;
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_90904) h_90907);
    (Litex.add _wd_2_0 _wd_2_1 (Litex.positiveRealToComplex _wd_2_0 h_90904) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _wd_2_0 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _wd_2_0 h_90904) (_atomic_wd_1_0).wd.2.2))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.addInC _value_i26 (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex _value_i26 h_90904) (Litex.divInC _wd_1_1 _value_i26 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i26 h_90904) ((_atomic_wd_1_0).val.right).wd.2.2))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

    have h_90746 : (by
      let _equal_wd_1_0 := _object_w185
      let _equal_wd_1_1 := _object_w186
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w185;
            let _equal_wd_1_1 := _object_w186;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i26)) = (M.divValue (M.addValue (Litex.denote _value_i26) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i26))) (M.number (2 : ℂ))) from by
              have _litex_residual : (M.divValue (M.addValue (Litex.denote _value_i26) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i26))) (M.number (2 : ℂ))) = (M.divValue (M.addValue (Litex.denote _value_i26) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i26))) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i26)))).trans (by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
              let _wd_1_1 := _value_i26;
              (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _wd_1_1 h_90904) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_1)).mp h_90904).2))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_7460 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (M.divValue (M.addValue _raw_i5 (M.divValue (M.number (2 : ℂ)) _raw_i5)) (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i26) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i26))) (M.number (2 : ℂ))) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w187 := (let _wd_1_0 := _object_w185;
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w185
      exact (Litex.positiveRealToComplex _object_w185 (Litex.callInOutput _object_w185))) (Litex.numberInC (M := M) (1 : ℂ))))

    let _object_w188 := (let _wd_1_0 := _object_w186;
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w186
      exact (Litex.divInC (_object_w186).val.left (Litex.number (M := M) (2 : ℂ)) (Litex.addInC _value_i26 ((_object_w186).val.left).val.right (Litex.positiveRealToComplex _value_i26 h_90904) (Litex.divInC (Litex.number (M := M) (2 : ℂ)) _value_i26 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i26 h_90904) (((_object_w186).val.left).val.right).wd.2.2)) (Litex.numberInC (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.2.2)) (Litex.numberInC (M := M) (1 : ℂ))))

    have h_90747 : (by
      let _equal_wd_1_0 := _object_w187
      let _equal_wd_1_1 := _object_w188
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _value_i26)) = (M.divValue (M.addValue (Litex.denote _value_i26) (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i26))) (M.number (2 : ℂ))) from h_90746) (show (M.number (1 : ℂ)) = (M.number (1 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))
          )
      )
    let _object_w189 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.sub _value_i26 (Litex.number (M := M) (1 : ℂ)) (Litex.positiveRealToComplex _value_i26 h_90904) (Litex.numberInC (M := M) (1 : ℂ)));
    let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_3_0
      exact (Litex.subInR _value_i26 (Litex.number (M := M) (1 : ℂ)) (Litex.inRPos_real _value_i26 h_90904) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_1_0 := _wd_2_0
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.subInC _value_i26 _wd_2_1 (Litex.positiveRealToComplex _value_i26 h_90904) (Litex.numberInC (M := M) (1 : ℂ)))
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.numberInC (M := M) (1 : ℂ))));
    let _wd_1_1 := _object_w184;
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (by
        let _litex_power := (_atomic_wd_1_0).val.left
        have _elaborated_power_base := (Litex.subInC _value_i26 (Litex.number (M := M) (1 : ℂ)) (Litex.positiveRealToComplex _value_i26 h_90904) (Litex.numberInC (M := M) (1 : ℂ)))
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      ) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_1_0 := _object_w184
      exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) _value_i26 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i26 h_90904))) (by
      let _atomic_wd_1_0 := _object_w184
      exact h_90745)))

    have h_90748 : (by
      let _equal_wd_1_0 := _object_w188
      let _equal_wd_1_1 := _object_w189
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w188;
            let _equal_wd_1_1 := _object_w189;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((((Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904)) + ((2 : ℂ) / (Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904)))) / (2 : ℂ)) - (1 : ℂ)) (((((Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904)) - (1 : ℂ)) ^ (2 : ℕ)) + (1 : ℂ)) / ((2 : ℂ) * (Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904)))) (Litex.NativeBridge.denoteSub (_object_w188).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w188).wd.1 (_object_w188).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w186).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w186).wd.1 (_object_w186).wd.2.1 (_object_w186).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i26 ((_object_w186).val.left).val.right ((_object_w186).val.left).wd.1 ((_object_w186).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) _value_i26 (((_object_w186).val.left).val.right).wd.1 (((_object_w186).val.left).val.right).wd.2.1 (((_object_w186).val.left).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd ((_equal_wd_1_1).val.left).val.left (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_1).val.left).wd.1 ((_equal_wd_1_1).val.left).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal (((_equal_wd_1_1).val.left).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_1_0 := (((_equal_wd_1_1).val.left).val.left).val.base
              exact (Litex.subInR _value_i26 (Litex.number (M := M) (1 : ℂ)) (Litex.inRPos_real _value_i26 h_90904) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub _value_i26 (Litex.number (M := M) (1 : ℂ)) ((((_equal_wd_1_1).val.left).val.left).val.base).wd.1 ((((_equal_wd_1_1).val.left).val.left).val.base).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) _value_i26 (_object_w184).wd.1 (_object_w184).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904)))) (by
              have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i26 (Litex.NativeBridge.asComplex _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904)) (Litex.NativeBridge.asComplex_spec _value_i26 (Litex.positiveRealToComplex _value_i26 h_90904)) h_90907
              have _litex_nz_1 : ((2 : ℂ) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
              litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | exact _litex_nz_1 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
            ))))
          )
      )
    have h_90749 : (by
      let _equal_wd_1_0 := _object_w187
      let _equal_wd_1_1 := _object_w189
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            ((h_90747).trans h_90748)
          )
      )
    let _object_w190 := ((_object_w189).val.left).val.left

    have h_90750 : (by
      let _atomic_wd_1_0 := _object_w190
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w190
              exact (by
                let _atomic_wd_2_1 := _atomic_wd_1_0
                exact (Litex.powStructuralNonnegativeOfEven _atomic_wd_2_1 (by
                  let _atomic_wd_3_0 := (_atomic_wd_2_1).val.base
                  exact (Litex.subInR _value_i26 (Litex.number (M := M) (1 : ℂ)) (Litex.inRPos_real _value_i26 h_90904) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num))))
          )
      )
    let _object_w191 := (let _wd_1_0 := _object_w190;
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w190
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.subInC _value_i26 _wd_1_1 (Litex.positiveRealToComplex _value_i26 h_90904) (Litex.numberInC (M := M) (1 : ℂ)))
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.numberInC (M := M) (1 : ℂ))))

    have h_90751 : (by
      let _atomic_wd_1_0 := _object_w191
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w191
              exact (by
                let _litex_zero_bound := _atomic_wd_1_0
                exact Litex.addPositiveRight _litex_zero_bound.val.left _litex_zero_bound.val.right _litex_zero_bound.wd.1 _litex_zero_bound.wd.2 (by
                let _atomic_wd_2_1 := _object_w190
                exact h_90750) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
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
    have h_90752 : (by
      let _atomic_wd_1_0 := _object_w184
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w184
              exact (by
                let _litex_positive_result := _atomic_wd_1_0
                exact Litex.mulPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_90905
              ))
          )
      )
    have h_90753 : (by
      let _atomic_wd_1_0 := _object_w189
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w189
              exact (by
                let _litex_positive_result := _atomic_wd_1_0
                exact Litex.divPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2.1 _litex_positive_result.wd.2.2 (by
                let _atomic_wd_2_1 := _object_w191
                exact h_90751) (by
                let _atomic_wd_2_1 := _object_w184
                exact h_90752)
              ))
          )
      )
    have h_90754 : (by
      let _atomic_wd_1_0 := _object_w187
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w187
              exact (Litex.ltOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w189 _atomic_wd_1_0 (show @Eq M.Value _ _ from Eq.refl _) (h_90749).symm h_90753))
          )
      )
    exact (by
      let _atomic_wd_1_0 := _object_w185
      exact (by
        let _atomic_wd_2_1 := _object_w185
        exact (Litex.subPositiveToLt _object_w187 (by
          let _atomic_wd_3_0 := _object_w185
          exact (Litex.inRPos_real _object_w185 (Litex.callInOutput _object_w185))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.ltOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w189 _object_w187 (show @Eq M.Value _ _ from Eq.refl _) (h_90749).symm h_90753))))
  )

theorem h_105933 : ∀ {_Host_i28 : Type v28} [_rep_i28 : Litex.Representation M _Host_i28] (_value_i28 : Litex.Obj (M := M) _Host_i28) (h_105938 : Litex.In _value_i28 (Litex.N (M := M))), (by
  let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i28 (h_10028 (M := M)) h_105938 True.intro)
  exact Litex.Le (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0) :=
  (by
    intro _Host_i28 _rep_i28 _value_i28 h_105938
    have h_105939 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i28 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i28 h_105938)
          )
      )
    have h_106085 : Litex.In _value_i28 (Litex.N (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_105938
          )
      )
    have h_106086 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i28 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i28 h_106085)
          )
      )
    have h_114290 : ∀ (_raw_i29 : M.Value) (h_106100 : M.mem _raw_i29 (M.standard .integer)) (h_106101 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i29 = M.number (_s : ℂ) ∧ _r ≤ _s)), (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i29) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
      (by
        litex_checked_step =>
          exact (
            (by
              intro _raw_i29 h_106100 h_106101
              let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_106100)
              have h_106152 : Litex.In _value_i29 (Litex.N (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i29 h_106100 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                        have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                        have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_106101)
                    )
                )
              exact Litex.integerInductionFromZero (fun (_raw_i29 : M.Value) => (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i29) = M.number (_s : ℂ) ∧ _r ≤ _s)) (by
                let _raw_i29 : M.Value := M.number 0
                have h_106387 : M.mem _raw_i29 (M.standard .integer) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num))
                let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_106387)
                have h_106387 : Litex.In _value_i29 (Litex.Z (M := M)) := h_106387
                have h_106388 : Litex.Same _value_i29 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by rfl)
                      )
                  )
                let _object_w199 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_10028 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)

                have h_105935 : (by
                  let _equal_wd_1_0 := _object_w199
                  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := _object_w199;
                        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (by
                          let _checked_call := _equal_wd_1_0
                          have _checked_case_guard : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
                          have _selected_beta := (h_10030 (M := M)) _checked_call.val.argument _checked_call.wd.2.1 _checked_case_guard
                          exact _selected_beta.trans (show @Eq M.Value _ _ from Eq.refl _))))
                      )
                  )
                show (fun (_raw_i29 : M.Value) => (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i29) = M.number (_s : ℂ) ∧ _r ≤ _s)) (M.number 0)
                exact (by
                  let _atomic_wd_1_0 := _object_w199
                  exact (Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0 (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (h_105935).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_right_value _litex_left_value) (by norm_num)))))
              ) (by
                intro _raw_i29 _induction_integer _induction_nonnegative _induction_hypothesis
                have h_106680 : M.mem _raw_i29 (M.standard .integer) := _induction_integer
                let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_106680)
                have h_106680 : Litex.In _value_i29 (Litex.Z (M := M)) := h_106680
                have h_106681 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i29 :=
                  (by
                    litex_checked_step =>
                      exact (
                        _induction_nonnegative
                      )
                  )
                have h_106732 : Litex.In _value_i29 (Litex.N (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i29 h_106680 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_106681)
                      )
                  )
                have h_105934 : Litex.Le (Litex.number (M := M) (1 : ℂ)) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _induction_hypothesis
                      )
                  )
                let _object_w209 := (let _object_w205 := (Litex.add _value_i29 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i29 h_106680) (Litex.numberInC (M := M) (1 : ℂ)));
                (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _object_w205 (h_10028 (M := M)) (by
                  let _atomic_wd_1_0 := _object_w205
                  exact (Litex.addInN _value_i29 (Litex.number (M := M) (1 : ℂ)) h_106732 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))

                let _object_w210 := (let _wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro);
                (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _wd_1_0 (h_7459 (M := M)) (Litex.inRPos_real _wd_1_0 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (by
                    let _litex_return_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro)
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _wd_1_0)).mp (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (by
                    let _litex_return_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro)
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))).2))

                have h_105936 : (by
                  let _equal_wd_1_0 := _object_w209
                  let _equal_wd_1_1 := _object_w210
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          have h_113561 : Litex.In _value_i29 (Litex.N (M := M)) :=
                            h_106732
                          exact (Eq.trans (Eq.symm (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i8 (M := M))) (congrArg₂ M.addValue (Litex.sameRefl _value_i29) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))))) (Eq.trans ((h_24199 (M := M)) _value_i29 h_113561) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i8 (M := M))) (Litex.sameRefl _value_i29)))))
                        )
                      )
                  )
                have h_113571 : Litex.Lt (Litex.number (M := M) (1 : ℂ)) _object_w210 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          have h_113570 : (by
                            let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro)
                            exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro)
                                    exact (by
                                      let _litex_return_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro)
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))
                                )
                            )
                          have h_113643 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inRPos_positive (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro) h_113570)
                                )
                            )
                          have h_113644 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.ltToLe (Litex.number (M := M) 0) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro) h_113643)
                                )
                            )
                          have h_113645 : ¬ Litex.Same (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro) (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro) h_113643) _litex_zero.symm)
                                )
                            )
                          exact ((h_90742 (M := M)) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i29 (h_10028 (M := M)) h_106732 True.intro) h_113570)
                        )
                      )
                  )

                have h_114055 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_w210 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _object_w210 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_113571)
                      )
                  )
                have h_105937 : (by
                  let _atomic_wd_1_0 := _object_w210
                  exact Litex.Lt (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w210
                          exact h_113571)
                      )
                  )

                have h_114099 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_w210 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _object_w210 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_105937)
                      )
                  )
                show (fun (_raw_i29 : M.Value) => (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i29) = M.number (_s : ℂ) ∧ _r ≤ _s)) (M.addValue _raw_i29 (M.number 1))
                exact (by
                  let _atomic_wd_1_0 := _object_w209
                  exact (Litex.ltToLe (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0 (Litex.ltOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _object_w210 _atomic_wd_1_0 (show @Eq M.Value _ _ from Eq.refl _) (h_105936).symm h_113571)))
              ) _value_i29 h_106100 h_106101
            )
          )
      )
    exact (by
      let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i28 (h_10028 (M := M)) h_106085 True.intro)
      exact (by
        have h_114758 : Litex.In _value_i28 (Litex.Z (M := M)) :=
          (Litex.naturalToInteger _value_i28 h_106085)
        have h_114783 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i28 :=
          h_106086
        exact (Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0 _atomic_wd_1_0 (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i8 (M := M))) (Litex.sameRefl _value_i28)) ((fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value : Litex.Obj (M := M) _Host) => h_114290 (Litex.denote _value)) _value_i28 h_114758 h_114783))
      ))
  )

theorem h_114980 : ∀ {_Host_i31 : Type v31} [_rep_i31 : Litex.Representation M _Host_i31] (_value_i31 : Litex.Obj (M := M) _Host_i31) (h_114987 : Litex.In _value_i31 (Litex.N (M := M))), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
  let _wd_2_1 := (let _wd_3_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i31 (h_10028 (M := M)) h_114987 True.intro);
  let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_3_0
    exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (by
      let _arithmetic := _atomic_wd_1_0
      exact Litex.powObjInC _arithmetic))));
  let _wd_1_1 := (let _object_w216 := (Litex.add _value_i31 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i31 h_114987) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w216 (h_10610 (M := M)) (by
    let _atomic_wd_1_0 := _object_w216
    exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_114987 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro));
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _arithmetic := _atomic_wd_1_0
      exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i31 (h_10610 (M := M)) h_114987 True.intro);
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    intro _Host_i31 _rep_i31 _value_i31 h_114987
    have h_114988 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i31 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i31 h_114987)
          )
      )
    have h_116510 : Litex.In _value_i31 (Litex.N (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_114987
          )
      )
    have h_116511 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i31 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i31 h_116510)
          )
      )
    let _object_w226 := (let _object_w219 := (Litex.add _value_i31 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i31 h_116510) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _object_w219 (h_10028 (M := M)) (by
      let _atomic_wd_1_0 := _object_w219
      exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_116510 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))

    let _object_w227 := (let _object_w220 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i31 (h_10028 (M := M)) h_116510 True.intro);
    (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _object_w220 (h_7459 (M := M)) (Litex.inRPos_real _object_w220 (by
      let _atomic_wd_1_0 := _object_w220
      exact (by
        let _litex_return_call := _object_w220
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w220)).mp (by
      let _atomic_wd_1_0 := _object_w220
      exact (by
        let _litex_return_call := _object_w220
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))).2))

    have h_114981 : (by
      let _equal_wd_1_0 := _object_w226
      let _equal_wd_1_1 := _object_w227
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_122349 : Litex.In _value_i31 (Litex.N (M := M)) :=
                h_116510
              exact (Eq.trans (Eq.symm (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i8 (M := M))) (congrArg₂ M.addValue (Litex.sameRefl _value_i31) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))))) (Eq.trans ((h_24199 (M := M)) _value_i31 h_122349) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i4 (M := M))) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i8 (M := M))) (Litex.sameRefl _value_i31)))))
            )
          )
      )
    have h_114982 : (by
      let _chain_wd_114982_0 := (let _object_w228 := (_object_w226).val.argument;
      (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w228 (h_10610 (M := M)) (by
        let _atomic_wd_1_0 := _object_w228
        exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_116510 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
      let _chain_wd_114982_1 := (let _wd_1_0 := (let _wd_2_0 := _object_w226;
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_96 (M := M)) (by
        let _atomic_wd_1_0 := _object_w226
        exact (Litex.inRPos_real _object_w226 (Litex.callInOutput _object_w226))) True.intro));
      (Litex.abs _wd_1_0 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (by
          let _litex_return_call := _atomic_wd_1_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
      let _chain_wd_114982_2 := _chain_wd_114982_1
      let _chain_wd_114982_3 := (let _wd_1_0 := (let _wd_2_0 := _object_w227;
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_96 (M := M)) (by
        let _atomic_wd_1_0 := _object_w227
        exact (Litex.inRPos_real _object_w227 (Litex.callInOutput _object_w227))) True.intro));
      (Litex.abs _wd_1_0 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (by
          let _litex_return_call := _atomic_wd_1_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
      exact ((by
        let _equal_wd_1_0 := _chain_wd_114982_0
        let _equal_wd_1_1 := _chain_wd_114982_1
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
        let _equal_wd_1_0 := _chain_wd_114982_2
        let _equal_wd_1_1 := _chain_wd_114982_3
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _chain_wd_114982_0 := (let _object_w228 := (_object_w226).val.argument;
              (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w228 (h_10610 (M := M)) (by
                let _atomic_wd_1_0 := _object_w228
                exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_116510 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
              let _chain_wd_114982_1 := (let _wd_1_0 := (let _wd_2_0 := _object_w226;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_96 (M := M)) (by
                let _atomic_wd_1_0 := _object_w226
                exact (Litex.inRPos_real _object_w226 (Litex.callInOutput _object_w226))) True.intro));
              (Litex.abs _wd_1_0 (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (by
                  let _litex_return_call := _atomic_wd_1_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
              let _chain_wd_114982_2 := _chain_wd_114982_1
              let _chain_wd_114982_3 := (let _wd_1_0 := (let _wd_2_0 := _object_w227;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_2_0 (h_96 (M := M)) (by
                let _atomic_wd_1_0 := _object_w227
                exact (Litex.inRPos_real _object_w227 (Litex.callInOutput _object_w227))) True.intro));
              (Litex.abs _wd_1_0 (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (by
                  let _litex_return_call := _atomic_wd_1_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
              exact (And.intro (let _equal_wd_1_0 := _chain_wd_114982_0;
              let _equal_wd_1_1 := _chain_wd_114982_1;
              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))))) from by
                have _litex_residual : (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))))) := (show @Eq M.Value _ _ from Eq.refl _)
                exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))))).trans (by
                let _litex_original := _equal_wd_1_0
                let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
                let _object_w232 := (_equal_wd_1_0).val.argument;
                (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _wd_1_0 _object_w232 (Litex.formulaFnInFnSet _wd_1_0) (by
                  let _atomic_wd_1_0 := _object_w232
                  exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_116510 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_10611 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (Litex.denote _litex_literal.val.argument) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))))) from rfl))
              ))).trans _litex_residual))) (congrArg (Litex.absValue (M := M)) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ))))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)))) from (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_114981)))))
          )
      )

    have h_125678 :=
      (And.left h_114982)

    have h_125679 :=
      (And.right h_114982)

    have h_125680 :=
      h_125678

    have h_125681 :=
      h_125679

    have h_125682 :=
      (Eq.trans h_125678 h_125679)
    let _object_w239 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i31 (h_10610 (M := M)) h_116510 True.intro)

    let _object_w240 := (let _wd_1_0 := (let _object_w233 := (_object_w227).val.argument;
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w233 (h_96 (M := M)) (by
      let _atomic_wd_1_0 := _object_w233
      exact (Litex.inRPos_real _object_w233 (Litex.callInOutput _object_w233))) True.intro));
    (Litex.abs _wd_1_0 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))

    have h_114983 : (by
      let _equal_wd_1_0 := _object_w239
      let _equal_wd_1_1 := _object_w240
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w239;
            let _equal_wd_1_1 := _object_w240;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i31)) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)))) from by
              have _litex_residual : (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i31)))).trans (by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
              let _wd_1_1 := _value_i31;
              (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_116510 True.intro))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_10611 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (Litex.denote _litex_literal.val.argument) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)))) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w259 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_2_1 := (let _wd_3_0 := ((_object_w240).val.arg).val.argument;
    let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_3_0
      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (by
        let _arithmetic := _atomic_wd_1_0
        exact Litex.powObjInC _arithmetic))));
    let _wd_1_1 := (let _object_w241 := (_object_w226).val.argument;
    (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w241 (h_10610 (M := M)) (by
      let _atomic_wd_1_0 := _object_w241
      exact (Litex.addInN _value_i31 (Litex.number (M := M) (1 : ℂ)) h_116510 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro));
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (by
        let _arithmetic := _atomic_wd_1_0
        exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))

    let _object_w260 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_2_1 := (let _wd_3_0 := ((_object_w240).val.arg).val.argument;
    let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_3_0
      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (by
        let _arithmetic := _atomic_wd_1_0
        exact Litex.powObjInC _arithmetic))));
    let _wd_1_1 := (let _wd_2_0 := (let _wd_3_0 := _object_w227;
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_3_0 (h_96 (M := M)) (by
      let _atomic_wd_1_0 := _object_w227
      exact (Litex.inRPos_real _object_w227 (Litex.callInOutput _object_w227))) True.intro));
    (Litex.abs _wd_2_0 (by
      let _atomic_wd_1_0 := _wd_2_0
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

    have h_114984 : (by
      let _equal_wd_1_0 := _object_w259
      let _equal_wd_1_1 := _object_w260
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ M.mulValue (show (M.mulValue (M.number (4 : ℂ)) (M.powValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)) (M.number (2 : ℂ)))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)) (M.number (2 : ℂ)))) from (show @Eq M.Value _ _ from Eq.refl _)) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.addValue (Litex.denote _value_i31) (M.number (1 : ℂ)))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31))))) from h_125682))
          )
      )
    let _object_w261 := (let _wd_1_0 := _object_w239;
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _object_w239
      exact (by
        let _litex_return_call := _object_w239
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

    let _object_w262 := (let _wd_1_0 := _object_w240;
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _object_w240
      exact (by
        let _litex_abs := _atomic_wd_1_0
        exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
      )) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

    have h_114985 : (by
      let _equal_wd_1_0 := _object_w261
      let _equal_wd_1_1 := _object_w262
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ M.powValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i31)) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i31)))) from h_114983) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))
          )
      )
    have h_153140 : Litex.Same _object_w260 _object_w262 :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_153139 : (by
                let _atomic_wd_1_0 := (((_object_w259).val.left).val.right).val.base
                exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M))) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        let _atomic_wd_1_0 := (((_object_w259).val.left).val.right).val.base
                        exact (by
                          let _litex_return_call := _atomic_wd_1_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))
                    )
                )
              have h_153201 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (((_object_w259).val.left).val.right).val.base :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inRPos_positive (((_object_w259).val.left).val.right).val.base h_153139)
                    )
                )
              have h_153202 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (((_object_w259).val.left).val.right).val.base :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.ltToLe (Litex.number (M := M) 0) (((_object_w259).val.left).val.right).val.base h_153201)
                    )
                )
              have h_153203 : ¬ Litex.Same (((_object_w259).val.left).val.right).val.base (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (((_object_w259).val.left).val.right).val.base h_153201) _litex_zero.symm)
                    )
                )
              exact ((h_71947 (M := M)) (((_object_w259).val.left).val.right).val.base h_153139)
            )
          )
      )
    have h_114986 : (by
      let _equal_wd_1_0 := _object_w260
      let _equal_wd_1_1 := _object_w262
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            h_153140
          )
      )
    exact ((((h_114984).trans h_153140)).trans (h_114985).symm)
  )

theorem h_156832 : ∀ {_Host_i33 : Type v33} [_rep_i33 : Litex.Representation M _Host_i33] (_value_i33 : Litex.Obj (M := M) _Host_i33) (h_156858 : Litex.In _value_i33 (Litex.N (M := M))), (by
  let _atomic_wd_1_0 := (let _object_w272 := (Litex.add _value_i33 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i33 h_156858) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w272 (h_10610 (M := M)) (by
    let _atomic_wd_2_0 := _object_w272
    exact (Litex.addInN _value_i33 (Litex.number (M := M) (1 : ℂ)) h_156858 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
  let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i33 (h_10610 (M := M)) h_156858 True.intro);
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
    intro _Host_i33 _rep_i33 _value_i33 h_156858
    have h_156859 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i33 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i33 h_156858)
          )
      )
    have h_158632 : Litex.In _value_i33 (Litex.N (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_156858
          )
      )
    have h_158633 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i33 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i33 h_158632)
          )
      )
    have h_158635 : Litex.Le (Litex.number (M := M) (1 : ℂ)) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_158634 : Litex.In _value_i33 (Litex.N (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      h_158632
                    )
                )
              have h_158640 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i33 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.naturalNonnegative _value_i33 h_158634)
                    )
                )
              exact ((h_105933 (M := M)) _value_i33 h_158634)
            )
          )
      )
    have h_156833 : (by
      let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)
      exact Litex.Le (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)
              exact h_158635)
          )
      )
    let _object_w277 := (let _wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro);
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.positiveRealToComplex (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)))) (Litex.numberInC (M := M) (1 : ℂ))))

    have h_156834 : (by
      let _atomic_wd_1_0 := _object_w277
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w277
              exact (by
                let _litex_real_result := _atomic_wd_1_0
                exact Litex.subInR _litex_real_result.val.left _litex_real_result.val.right (by
                let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
              ))
          )
      )
    let _object_w279 := (let _wd_1_0 := (_object_w277).val.left;
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.positiveRealToComplex (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)))) (Litex.numberInC (M := M) (1 : ℂ))))

    have h_156835 : (by
      let _atomic_wd_1_0 := _object_w279
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w279
              exact (by
                let _litex_real_result := _atomic_wd_1_0
                exact Litex.addInR _litex_real_result.val.left _litex_real_result.val.right (by
                let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
              ))
          )
      )
    have h_156836 : (by
      let _atomic_wd_1_0 := _object_w277
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w277
              exact (Litex.subNonnegative _atomic_wd_1_0 h_158635))
          )
      )
    have h_156837 : (by
      let _atomic_wd_1_0 := _object_w279
      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w279
              exact (by
                let _litex_positive_result := _atomic_wd_1_0
                exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 (by
                let _atomic_wd_2_0 := (_object_w279).val.left
                exact (Litex.inRPos_positive _atomic_wd_2_0 (by
                  let _atomic_wd_3_0 := _atomic_wd_2_0
                  exact (by
                    let _litex_return_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)
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
    have h_156838 : (by
      let _atomic_wd_1_0 := _object_w279
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w279
              exact (Litex.ltToLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0 h_156837))
          )
      )
    let _object_w281 := (let _wd_1_0 := _object_w277;
    let _wd_1_1 := _object_w279;
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w277
      exact (M.real_subset_complex _ h_156834)) (by
      let _atomic_wd_1_0 := _object_w279
      exact (M.real_subset_complex _ h_156835))))

    have h_156839 : (by
      let _atomic_wd_1_0 := _object_w281
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w281
              exact (by
                let _litex_zero_bound := _atomic_wd_1_0
                exact Litex.mulNonnegative _litex_zero_bound.val.left _litex_zero_bound.val.right _litex_zero_bound.wd.1 _litex_zero_bound.wd.2 (by
                let _atomic_wd_2_1 := _object_w277
                exact h_156836) (by
                let _atomic_wd_2_1 := _object_w279
                exact h_156838)
              ))
          )
      )
    have h_156840 : (by
      let _chain_wd_156840_0 := (let _wd_1_0 := (let _wd_2_0 := (_object_w279).val.left;
      let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
        let _atomic_wd_1_0 := _wd_2_0
        exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
      let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
      (Litex.sub _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (by
          let _arithmetic := _atomic_wd_1_0
          exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (1 : ℂ))))
      let _chain_wd_156840_1 := _object_w281
      exact ((by
        let _equal_wd_1_0 := _chain_wd_156840_0
        let _equal_wd_1_1 := _chain_wd_156840_1
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
        let _atomic_wd_1_0 := _object_w281
        exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _chain_wd_156840_0 := (let _wd_1_0 := (let _wd_2_0 := (_object_w279).val.left;
              let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                let _atomic_wd_1_0 := _wd_2_0
                exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
              let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
              (Litex.sub _wd_1_0 _wd_1_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (by
                  let _arithmetic := _atomic_wd_1_0
                  exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (1 : ℂ))))
              let _chain_wd_156840_1 := _object_w281
              exact (And.intro (let _equal_wd_1_0 := _chain_wd_156840_0;
              let _equal_wd_1_1 := _chain_wd_156840_1;
              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro);
              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) ^ (2 : ℕ)) - (1 : ℂ)) (((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro);
              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) - (1 : ℂ)) * ((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro);
              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (1 : ℂ))) (Litex.NativeBridge.denoteSub (_equal_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                let _atomic_wd_1_0 := ((_equal_wd_1_0).val.left).val.base
                exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro);
              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
              Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteMul _object_w277 _object_w279 (by
                let _atomic_wd_1_0 := _object_w277
                exact (M.real_subset_complex _ h_156834)) (by
                let _atomic_wd_1_0 := _object_w279
                exact (M.real_subset_complex _ h_156835)) _ _ (Litex.NativeBridge.denoteSub (_object_w277).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w277).wd.1 (_object_w277).wd.2 _ _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro);
              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
              Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteAdd (_object_w279).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w279).wd.1 (_object_w279).wd.2 _ _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro);
              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
              Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (by ring!)))) (by
                let _atomic_wd_1_0 := _object_w281
                exact h_156839)))
          )
      )

    have h_161693 :=
      (And.left h_156840)

    have h_161694 :=
      (And.right h_156840)

    have h_161695 :=
      h_161693

    have h_161696 :=
      h_161694

    have h_161823 :=
      (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w281 (let _wd_1_0 := (let _wd_2_0 := (_object_w279).val.left;
      let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
        let _atomic_wd_1_0 := _wd_2_0
        exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
      let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
      (Litex.sub _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (by
          let _arithmetic := _atomic_wd_1_0
          exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (Eq.symm h_161693) h_161694)
    let _object_w282 := (let _wd_1_0 := (let _wd_2_0 := (_object_w279).val.left;
    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_2_0
      exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (by
        let _arithmetic := _atomic_wd_1_0
        exact Litex.powObjInC _arithmetic)) (Litex.numberInC (M := M) (1 : ℂ))))

    have h_156841 : (by
      let _atomic_wd_1_1 := _object_w282
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_1 := _object_w282
              exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w281 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_161693).symm h_156839))
          )
      )
    let _object_w283 := (_object_w282).val.left

    have h_156842 : (by
      let _atomic_wd_1_1 := _object_w283
      exact Litex.Le (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_1 := _object_w283
              exact (Litex.subNonnegativeToLe _object_w282 (by
                let _atomic_wd_2_0 := _atomic_wd_1_1
                exact (Litex.powStructuralInR _atomic_wd_2_0 (by
                  let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
                  exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)))))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_156841))
          )
      )
    have h_156843 : (by
      let _atomic_wd_1_0 := _object_w283
      exact Litex.Le (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w283
              exact h_156842)
          )
      )
    let _object_w301 := (let _object_w284 := (Litex.add _value_i33 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i33 h_158632) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w284 (h_10610 (M := M)) (by
      let _atomic_wd_1_0 := _object_w284
      exact (Litex.addInN _value_i33 (Litex.number (M := M) (1 : ℂ)) h_158632 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))

    let _object_w302 := (let _wd_1_0 := (let _object_w286 := (let _object_w285 := (Litex.add _value_i33 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i33 h_158632) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _object_w285 (h_10028 (M := M)) (by
      let _atomic_wd_1_0 := _object_w285
      exact (Litex.addInN _value_i33 (Litex.number (M := M) (1 : ℂ)) h_158632 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w286 (h_96 (M := M)) (by
      let _atomic_wd_1_0 := _object_w286
      exact (Litex.inRPos_real _object_w286 (Litex.callInOutput _object_w286))) True.intro));
    (Litex.abs _wd_1_0 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))

    have h_156844 : (by
      let _equal_wd_1_0 := _object_w301
      let _equal_wd_1_1 := _object_w302
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w301;
            let _equal_wd_1_1 := _object_w302;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))))) from by
              have _litex_residual : (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))))).trans (by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
              let _object_w292 := (((_equal_wd_1_1).val.arg).val.argument).val.argument;
              (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _wd_1_0 _object_w292 (Litex.formulaFnInFnSet _wd_1_0) (by
                let _atomic_wd_1_0 := _object_w292
                exact (Litex.addInN _value_i33 (Litex.number (M := M) (1 : ℂ)) h_158632 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_10611 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (Litex.denote _litex_literal.val.argument) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.addValue (Litex.denote _value_i33) (M.number (1 : ℂ)))))) from rfl))
            ))).trans _litex_residual)))
          )
      )
    have h_156845 : (by
      let _atomic_wd_1_0 := _object_w302
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w302
              exact (by
                let _atomic_wd_2_1 := _object_w302
                exact (by
                  let _litex_abs := _atomic_wd_2_1
                  exact Litex.absNonnegative _litex_abs.val.arg _litex_abs.wd
                )))
          )
      )
    have h_156846 : (by
      let _atomic_wd_1_0 := _object_w301
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w301
              exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w302 _atomic_wd_1_0 (show @Eq M.Value _ _ from Eq.refl _) (h_156844).symm h_156845))
          )
      )
    have h_156847 : (by
      let _atomic_wd_1_0 := _object_w301
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w301
              exact (by
                let _litex_return_call := _object_w301
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
          )
      )
    have h_156848 : (by
      let _atomic_wd_1_0 := _object_w283
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w283
              exact (Litex.powStructuralInR _atomic_wd_1_0 (by
                let _atomic_wd_2_0 := (_object_w283).val.base
                exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro))))))
          )
      )
    have h_156849 : (by
      let _atomic_wd_1_1 := _object_w301
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_1 := _object_w301
              exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w302 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_156844).symm h_156845))
          )
      )
    let _object_w303 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
    let _wd_1_1 := _object_w301;
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
      let _atomic_wd_1_0 := _object_w301
      exact (M.real_subset_complex _ h_156847))))

    let _object_w304 := (let _wd_1_0 := _object_w283;
    let _wd_1_1 := _object_w301;
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w283
      exact (M.real_subset_complex _ h_156848)) (by
      let _atomic_wd_1_0 := _object_w301
      exact (M.real_subset_complex _ h_156847))))

    have h_156850 : (by
      let _atomic_wd_1_0 := _object_w303
      let _atomic_wd_1_1 := _object_w304
      exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w303
              let _atomic_wd_1_1 := _object_w304
              exact (by
                let _litex_monotone_left := _atomic_wd_1_0
                let _litex_monotone_right := _atomic_wd_1_1
                exact Litex.mulStructuralLeRight _litex_monotone_left _litex_monotone_right (by
                let _atomic_wd_2_1 := _object_w301
                exact h_156849) (by
                let _atomic_wd_2_1 := _object_w283
                exact h_156842) (Litex.sameRefl _litex_monotone_left.val.right)
              ))
          )
      )
    have h_156851 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) :=
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

    have h_178127 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
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
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_156851)
          )
      )
    let _object_w306 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_1_1 := _object_w303;
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _object_w303
      exact (Litex.mulInC (Litex.number (M := M) (1 : ℂ)) (_object_w303).val.right (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_156847)))))

    let _object_w307 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_1_1 := _object_w304;
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _object_w304
      exact (Litex.mulInC (_object_w304).val.left (_object_w303).val.right (M.real_subset_complex _ h_156848) (M.real_subset_complex _ h_156847)))))

    have h_156852 : (by
      let _atomic_wd_1_0 := _object_w306
      let _atomic_wd_1_1 := _object_w307
      exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w306
              let _atomic_wd_1_1 := _object_w307
              exact (by
                let _litex_monotone_left := _atomic_wd_1_0
                let _litex_monotone_right := _atomic_wd_1_1
                exact Litex.mulStructuralLeLeft _litex_monotone_left _litex_monotone_right h_156851 (by
                let _atomic_wd_2_0 := _object_w303
                let _atomic_wd_2_1 := _object_w304
                exact h_156850) (Litex.sameRefl _litex_monotone_left.val.left)
              ))
          )
      )
    let _object_w308 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_1_1 := _object_w301;
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _object_w301
      exact (M.real_subset_complex _ h_156847))))

    have h_156853 : (by
      let _equal_wd_1_0 := _object_w306
      let _equal_wd_1_1 := _object_w308
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w306;
            let _equal_wd_1_1 := _object_w308;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((4 : ℂ) * ((1 : ℂ) * (let _litex_numeric_call := _object_w301;
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
            Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member))) ((4 : ℂ) * (let _litex_numeric_call := _object_w301;
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
            Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) _object_w303 (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := _object_w303
              exact (Litex.mulInC (Litex.number (M := M) (1 : ℂ)) (_object_w303).val.right (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_156847))) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) _object_w301 (Litex.numberInC (M := M) (1 : ℂ)) (by
              let _atomic_wd_1_0 := _object_w301
              exact (M.real_subset_complex _ h_156847)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (let _litex_numeric_call := _object_w301;
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
            Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (let _litex_numeric_call := _object_w301;
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
            Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (by ring!))))
          )
      )

    have h_182822 : Litex.Same (_object_w306).val.right (_object_w308).val.right :=
      (by
        litex_checked_step =>
          exact (
            (Litex.mulCancelLeftLeft (_object_w306).val.right (_object_w308).val.right (Litex.number (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := _object_w303
              exact (Litex.mulInC (Litex.number (M := M) (1 : ℂ)) (_object_w308).val.right (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_156847))) (by
              let _atomic_wd_1_0 := _object_w301
              exact (M.real_subset_complex _ h_156847)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_156853)
          )
      )
    let _object_w309 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_2_1 := _object_w283;
    (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _object_w283
      exact (M.real_subset_complex _ h_156848))));
    let _wd_1_1 := _object_w301;
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (4 : ℂ)) (M.real_subset_complex _ h_156848))) (by
      let _atomic_wd_1_0 := _object_w301
      exact (M.real_subset_complex _ h_156847))))

    have h_156854 : (by
      let _equal_wd_1_0 := _object_w307
      let _equal_wd_1_1 := _object_w309
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w307;
            let _equal_wd_1_1 := _object_w309;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((4 : ℂ) * (((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro);
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
            Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) ^ (2 : ℕ)) * (let _litex_numeric_call := _object_w301;
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
            Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member))) (((4 : ℂ) * ((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro);
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
            Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) ^ (2 : ℕ))) * (let _litex_numeric_call := _object_w301;
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
            Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) _object_w304 (Litex.numberInC (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := _object_w304
              exact (Litex.mulInC (_object_w304).val.left (_object_w303).val.right (M.real_subset_complex _ h_156848) (M.real_subset_complex _ h_156847))) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteMul _object_w283 _object_w301 (by
              let _atomic_wd_1_0 := _object_w283
              exact (M.real_subset_complex _ h_156848)) (by
              let _atomic_wd_1_0 := _object_w301
              exact (M.real_subset_complex _ h_156847)) _ _ (Litex.NativeBridge.denotePowNatReal (_object_w283).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_1_0 := (_object_w283).val.base
              exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro);
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
            Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (let _litex_numeric_call := _object_w301;
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
            Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member))) (Litex.NativeBridge.denoteMul (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) ((_equal_wd_1_1).val.left).val.right ((_equal_wd_1_1).val.left).wd.1 ((_equal_wd_1_1).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denotePowNatReal (_object_w283).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_1_0 := (_object_w283).val.base
              exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i33 (h_10028 (M := M)) h_158632 True.intro);
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
            Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member))) (let _litex_numeric_call := _object_w301;
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
            Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (by ring!))))
          )
      )
    have h_156855 : (by
      let _atomic_wd_1_0 := _object_w308
      let _atomic_wd_1_1 := _object_w309
      exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w308
              let _atomic_wd_1_1 := _object_w309
              exact (Litex.leOfSame _object_w306 _atomic_wd_1_0 _object_w307 _atomic_wd_1_1 h_156853 h_156854 h_156852))
          )
      )
    have h_183376 : Litex.Same _object_w309 (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i33 (h_10610 (M := M)) h_158632 True.intro);
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
              have h_183375 : Litex.In _value_i33 (Litex.N (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      h_158632
                    )
                )
              have h_183381 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i33 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.naturalNonnegative _value_i33 h_183375)
                    )
                )
              exact ((h_114980 (M := M)) _value_i33 h_183375)
            )
          )
      )
    have h_156856 : (by
      let _equal_wd_1_0 := _object_w309
      let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i33 (h_10610 (M := M)) h_158632 True.intro);
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
            h_183376
          )
      )
    have h_156857 : (by
      let _atomic_wd_1_0 := _object_w308
      let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i33 (h_10610 (M := M)) h_158632 True.intro);
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
              let _atomic_wd_1_0 := _object_w308
              let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i33 (h_10610 (M := M)) h_158632 True.intro);
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (by
                  let _litex_return_call := _atomic_wd_1_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              exact (Litex.leOfSame _object_w306 _atomic_wd_1_0 _object_w307 _atomic_wd_1_1 h_156853 ((h_156854).trans h_183376) h_156852))
          )
      )
    exact (by
      let _atomic_wd_1_0 := _object_w301
      let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i33 (h_10610 (M := M)) h_158632 True.intro);
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
        let _litex_bound_product := _object_w308
        exact Litex.leDivOfProductBound _atomic_wd_1_0 _litex_bound_quotient _litex_bound_product (by
        let _atomic_wd_2_0 := _object_w301
        exact h_156847) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
        have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
          apply Complex.ofReal_injective
          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
        have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
          apply Complex.ofReal_injective
          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (by
        let _atomic_wd_2_0 := _object_w308
        let _atomic_wd_2_1 := (_atomic_wd_1_1).val.left
        exact (Litex.leOfSame _object_w306 _atomic_wd_2_0 _object_w307 _atomic_wd_2_1 h_156853 ((h_156854).trans h_183376) h_156852)) (Litex.sameRefl _litex_bound_product.val.left) (Litex.sameRefl _litex_bound_product.val.right)
      ))
  )

theorem h_198188 : ∀ {_Host_i35 : Type v35} [_rep_i35 : Litex.Representation M _Host_i35] (_value_i35 : Litex.Obj (M := M) _Host_i35) (h_198196 : Litex.In _value_i35 (Litex.N (M := M))), (by
  let _equal_wd_1_0 := (let _object_w315 := (Litex.add _value_i35 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i35 h_198196) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w315 (h_20132 (M := M)) (by
    let _atomic_wd_1_0 := _object_w315
    exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198196 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
  let _equal_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_198196 True.intro);
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
    intro _Host_i35 _rep_i35 _value_i35 h_198196
    have h_198197 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i35 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i35 h_198196)
          )
      )
    have h_198733 : Litex.In _value_i35 (Litex.N (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_198196
          )
      )
    have h_198734 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i35 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i35 h_198733)
          )
      )
    let _object_i36 := (let _wd_1_0 := (_object_w66 (M := M));
    let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) _value_i35 (Litex.NativeBridge.asNat _value_i35 h_198733) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_198733 (Litex.NativeBridge.asNat_spec _value_i35 h_198733));
    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_198733
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      ))) (by
      let _atomic_wd_1_0 := (_object_w66 (M := M))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_198733
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_198733
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      )))))
    have h_199620 : Litex.In _object_i36 (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := (let _wd_1_0 := (_object_w66 (M := M));
              let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) _value_i35 (Litex.NativeBridge.asNat _value_i35 h_198733) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_198733 (Litex.NativeBridge.asNat_spec _value_i35 h_198733));
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_2_0 := _wd_1_1
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ))) (by
                let _atomic_wd_2_0 := (_object_w66 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_2_0 := _wd_1_1
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_2_0 := _wd_1_1
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                )))))
              exact (Litex.inRPos_intro _atomic_wd_1_0 (by
                let _atomic_wd_2_0 := _atomic_wd_1_0
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_2_0).val.base ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))
                  have _elaborated_power_exponent := (by
                  let _litex_power := (_atomic_wd_2_0).val.exponent
                  have _elaborated_power_base := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
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
                  let _atomic_wd_3_1 := (_object_w66 (M := M))
                  exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_3_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                    let _atomic_wd_4_0 := (_object_w66 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_3_1 (by
                    let _atomic_wd_4_0 := (_object_w66 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (4 : ℝ)) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_3_1 (by
                    let _atomic_wd_4_0 := (_object_w66 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))))
          )
      )
    have h_199621 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_i36 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _object_i36 h_199620)
          )
      )
    have h_199622 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_i36 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _object_i36 h_199621)
          )
      )
    have h_199623 : ¬ Litex.Same _object_i36 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _object_i36 h_199621) _litex_zero.symm)
          )
      )
    have h_199624 : Litex.Same _object_i36 _object_i36 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.sameRefl (let _wd_1_0 := (_object_w66 (M := M));
            let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) _value_i35 (Litex.NativeBridge.asNat _value_i35 h_198733) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_198733 (Litex.NativeBridge.asNat_spec _value_i35 h_198733));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := (_object_w66 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ))))))
          )
      )
    have h_198189 : (by
      let _chain_wd_198189_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_198733 True.intro)
      let _chain_wd_198189_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
      let _wd_1_1 := _object_i36;
      (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _atomic_wd_1_0 := _object_i36
        exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620)))))
      let _chain_wd_198189_2 := _chain_wd_198189_1
      let _chain_wd_198189_3 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_199620))
      exact ((by
        let _equal_wd_1_0 := _chain_wd_198189_0
        let _equal_wd_1_1 := _chain_wd_198189_1
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
        let _equal_wd_1_0 := _chain_wd_198189_2
        let _equal_wd_1_1 := _chain_wd_198189_3
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _chain_wd_198189_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_198733 True.intro)
              let _chain_wd_198189_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
              let _wd_1_1 := _object_i36;
              (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _atomic_wd_1_0 := _object_i36
                exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620)))))
              let _chain_wd_198189_2 := _chain_wd_198189_1
              let _chain_wd_198189_3 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_199620))
              exact (And.intro (let _equal_wd_1_0 := _chain_wd_198189_0;
              let _equal_wd_1_1 := _chain_wd_198189_1;
              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (Litex.denote _value_i35)) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35)))) from by
                have _litex_residual : (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35)))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35)))) := (show @Eq M.Value _ _ from Eq.refl _)
                exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (Litex.denote _value_i35)))).trans (by
                let _litex_original := _equal_wd_1_0
                let _litex_literal := (let _wd_1_0 := (_object_i15 (M := M));
                let _wd_1_1 := _value_i35;
                (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_198733 True.intro))
                have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_20133 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35)))) from rfl))
              ))).trans _litex_residual))) (congrArg₂ M.mulValue (show (M.number (4 : ℂ)) = (M.number (4 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)) (show (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35))) = (Litex.denote _object_i36) from (h_199624).symm))))
          )
      )

    have h_200541 :=
      (And.left h_198189)

    have h_200542 :=
      (And.right h_198189)

    have h_200543 :=
      h_200541

    have h_200544 :=
      h_200542

    have h_200545 :=
      (Eq.trans h_200541 h_200542)
    let _object_w320 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
    let _wd_1_1 := (Litex.add _value_i35 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i35 h_198733) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))))) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))))))

    let _object_w321 := (let _wd_1_0 := (_object_i36).val.exponent;
    let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)));
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.numberInC (M := M) (2 : ℂ))
        have _elaborated_power_exponent := (Litex.naturalToInteger _value_i35 h_198733)
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) ^ (1 : ℕ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ))))))

    have h_198190 : (by
      let _equal_wd_1_0 := _object_w320
      let _equal_wd_1_1 := _object_w321
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w320;
            let _equal_wd_1_1 := _object_w321;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Eq.symm (by
              have _litex_base_complex : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.C (M := M)) := (Litex.numberInC (M := M) (2 : ℂ))
              have _litex_first_natural : Litex.In _value_i35 (Litex.N (M := M)) := h_198733
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

    have h_201220 : Litex.In _object_w321 (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_200950 : (by
              let _atomic_wd_1_1 := _object_w320
              exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
              let _atomic_wd_1_1 := _object_w320
              exact (Litex.powStructuralPositiveOfPositive _atomic_wd_1_1 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
              have h_201098 : (by
              let _atomic_wd_1_0 := (_object_w320).val.exponent
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) := (by
              let _atomic_wd_1_0 := (_object_w320).val.exponent
              exact (Litex.addInR _value_i35 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToReal _value_i35 h_198733) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))
              exact Litex.inOfSame _object_w320 _object_w321 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_198190 (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro _object_w320 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_200950; exact (M.real_members (Litex.denote _object_w320)).mpr ⟨_litex_real, _litex_value⟩) h_200950)
            )
          )
      )
    let _object_w322 := (_object_w321).val.right

    have h_198191 : (by
      let _equal_wd_1_0 := _object_w322
      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w322;
            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) ((2 : ℂ) ^ (1 : ℕ)) (2 : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
          )
      )

    have h_201322 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_201260 : (by
              let _atomic_wd_1_1 := _object_w322
              exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
              let _atomic_wd_1_1 := _object_w322
              exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                let _atomic_wd_2_0 := _object_w322
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (1 : ℕ)) (Litex.R (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) ^ (1 : ℕ)) (2 : ℝ) (by norm_num))))).mpr (by
                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                let _atomic_wd_2_0 := _object_w322
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (1 : ℕ)) (Litex.R (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) ^ (1 : ℕ)) (2 : ℝ) (by norm_num)))) = (2 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                let _atomic_wd_2_0 := _object_w322
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (1 : ℕ)) (Litex.R (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) ^ (1 : ℕ)) (2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (1 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) ((1 : ℕ) : ℂ)) (1 : ℂ) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
              have h_201303 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
              exact Litex.inOfSame _object_w322 (Litex.number (M := M) (2 : ℂ)) (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_198191 (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro _object_w322 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_201260; exact (M.real_members (Litex.denote _object_w322)).mpr ⟨_litex_real, _litex_value⟩) h_201260)
            )
          )
      )
    let _object_w324 := (let _wd_1_0 := (_object_w321).val.left;
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.numberInC (M := M) (2 : ℂ))
        have _elaborated_power_exponent := (Litex.naturalToInteger _value_i35 h_198733)
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.numberInC (M := M) (2 : ℂ))))

    have h_198192 : (by
      let _equal_wd_1_0 := _object_w320
      let _equal_wd_1_1 := _object_w324
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w320;
            let _equal_wd_1_1 := _object_w324;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Eq.symm (by
              have _litex_base_complex : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.C (M := M)) := (Litex.numberInC (M := M) (2 : ℂ))
              have _litex_first_natural : Litex.In _value_i35 (Litex.N (M := M)) := h_198733
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
                let _litex_exponent := (_object_w320).val.exponent
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

    have h_201800 : Litex.In _object_w324 (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_201521 : (by
              let _atomic_wd_1_1 := _object_w320
              exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
              let _atomic_wd_1_1 := _object_w320
              exact (Litex.powStructuralPositiveOfPositive _atomic_wd_1_1 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
              have h_201652 : (by
              let _atomic_wd_1_0 := (_object_w320).val.exponent
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) := (by
              let _atomic_wd_1_0 := (_object_w320).val.exponent
              exact (Litex.addInR _value_i35 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToReal _value_i35 h_198733) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))
              exact Litex.inOfSame _object_w320 _object_w324 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_198192 (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro _object_w320 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_201521; exact (M.real_members (Litex.denote _object_w320)).mpr ⟨_litex_real, _litex_value⟩) h_201521)
            )
          )
      )
    have h_198193 : (by
      let _chain_wd_198193_0 := (let _wd_1_0 := (_object_w66 (M := M));
      let _wd_1_1 := _object_w320;
      (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
        let _atomic_wd_1_0 := _object_w320
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
          have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
        ))) (by
        let _atomic_wd_1_0 := (_object_w66 (M := M))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
        let _atomic_wd_1_0 := _object_w320
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
          have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
        )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
        let _atomic_wd_1_0 := _object_w320
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
          have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
        )))))
      let _chain_wd_198193_1 := (let _wd_1_0 := (_object_w66 (M := M));
      let _wd_1_1 := _object_w324;
      (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
        let _atomic_wd_1_0 := _object_w324
        exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
          let _litex_power := (_object_w324).val.left
          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
          have _elaborated_power_exponent := h_198733
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
        let _atomic_wd_1_0 := (_object_w66 (M := M))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
        let _atomic_wd_1_0 := _object_w324
        exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
          let _litex_power := (_object_w324).val.left
          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
          have _elaborated_power_exponent := h_198733
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
        let _atomic_wd_1_0 := _object_w324
        exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
          let _litex_power := (_object_w324).val.left
          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
          have _elaborated_power_exponent := h_198733
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))))
      let _chain_wd_198193_2 := _chain_wd_198193_1
      let _chain_wd_198193_3 := (let _wd_1_0 := _object_i36;
      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
        let _atomic_wd_1_0 := _object_i36
        exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
      let _chain_wd_198193_4 := _chain_wd_198193_3
      let _chain_wd_198193_5 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
      exact ((by
        let _equal_wd_1_0 := _chain_wd_198193_0
        let _equal_wd_1_1 := _chain_wd_198193_1
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
        let _equal_wd_1_0 := _chain_wd_198193_2
        let _equal_wd_1_1 := _chain_wd_198193_3
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
        let _equal_wd_1_0 := _chain_wd_198193_4
        let _equal_wd_1_1 := _chain_wd_198193_5
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _chain_wd_198193_0 := (let _wd_1_0 := (_object_w66 (M := M));
              let _wd_1_1 := _object_w320;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w320
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ))) (by
                let _atomic_wd_1_0 := (_object_w66 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_1_0 := _object_w320
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w320
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                )))))
              let _chain_wd_198193_1 := (let _wd_1_0 := (_object_w66 (M := M));
              let _wd_1_1 := _object_w324;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                let _atomic_wd_1_0 := (_object_w66 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_1_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))))
              let _chain_wd_198193_2 := _chain_wd_198193_1
              let _chain_wd_198193_3 := (let _wd_1_0 := _object_i36;
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                let _atomic_wd_1_0 := _object_i36
                exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              let _chain_wd_198193_4 := _chain_wd_198193_3
              let _chain_wd_198193_5 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
              exact (And.intro (congrArg₂ M.powValue (show (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) from (show @Eq M.Value _ _ from Eq.refl _)) (show (M.powValue (M.number (2 : ℂ)) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))) = (M.mulValue (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35)) (M.number (2 : ℂ))) from h_198192)) (And.intro (let _equal_wd_1_0 := _chain_wd_198193_2;
              let _equal_wd_1_1 := _chain_wd_198193_3;
              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Eq.symm (by
                have _litex_base_complex : Litex.In (_equal_wd_1_0).val.base (Litex.C (M := M)) := (by
                let _atomic_wd_1_0 := (_object_w66 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (4 : ℂ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ)))))
                have _litex_first_natural : Litex.In (_object_w324).val.left (Litex.N (M := M)) := (by
                let _atomic_wd_1_0 := (_object_w324).val.left
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ))
                have _litex_second_natural : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                let _litex_base_value : ℂ := Litex.NativeBridge.asComplex (_equal_wd_1_0).val.base _litex_base_complex
                have _litex_base_denote : Litex.denote (_equal_wd_1_0).val.base = M.number _litex_base_value := Litex.NativeBridge.asComplex_spec (_equal_wd_1_0).val.base _litex_base_complex
                let _litex_n1 : ℕ := Litex.NativeBridge.asNat (_object_w324).val.left _litex_first_natural
                let _litex_n2 : ℕ := Litex.NativeBridge.asNat (Litex.number (M := M) (2 : ℂ)) _litex_second_natural
                have _litex_exp1 : Litex.Same (_object_w324).val.left (Litex.number (M := M) (_litex_n1 : ℂ)) := Litex.NativeBridge.asNat_spec (_object_w324).val.left _litex_first_natural
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
              )))) (congrArg₂ M.powValue (show (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (Litex.denote _value_i35))) = (Litex.denote _object_i36) from (h_199624).symm) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _))))))
          )
      )

    have h_202602 :=
      (And.left h_198193)

    have h_202603 :=
      (And.left (And.right h_198193))

    have h_202604 :=
      (And.right (And.right h_198193))

    have h_202605 :=
      h_202602

    have h_203152 : Litex.In (let _wd_1_0 := (_object_w66 (M := M));
    let _wd_1_1 := _object_w324;
    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w324
      exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
        let _litex_power := (_object_w324).val.left
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_198733
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
      let _atomic_wd_1_0 := (_object_w66 (M := M))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
      let _atomic_wd_1_0 := _object_w324
      exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
        let _litex_power := (_object_w324).val.left
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_198733
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w324
      exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
        let _litex_power := (_object_w324).val.left
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_198733
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_202608 : (by
              let _atomic_wd_1_1 := (let _wd_1_0 := (_object_w66 (M := M));
              let _wd_1_1 := _object_w320;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_2_0 := _object_w320
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ))) (by
                let _atomic_wd_2_0 := (_object_w66 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_2_0 := _object_w320
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_2_0 := _object_w320
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                )))))
              exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
              let _atomic_wd_1_1 := (let _wd_1_0 := (_object_w66 (M := M));
              let _wd_1_1 := _object_w320;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_2_0 := _object_w320
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ))) (by
                let _atomic_wd_2_0 := (_object_w66 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_2_0 := _object_w320
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_2_0 := _object_w320
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                )))))
              exact (Litex.powStructuralPositiveOfPositive _atomic_wd_1_1 (by
                let _atomic_wd_2_1 := (_object_w66 (M := M))
                exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                  let _atomic_wd_3_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).mpr (by
                  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                    apply Complex.ofReal_injective
                    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                  have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_2_1 (by
                  let _atomic_wd_3_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (4 : ℝ)) := by
                    apply Complex.ofReal_injective
                    exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_1 (by
                  let _atomic_wd_3_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
              have h_203091 : (by
              let _atomic_wd_1_0 := _object_w320
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) := (by
              let _atomic_wd_1_0 := _object_w320
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_w321 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (h_198190).symm (show @Eq M.Value _ _ from Eq.refl _) h_201220)))
              exact Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
            let _wd_1_1 := _object_w320;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w320
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := (_object_w66 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w320
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w320
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ))))) (let _wd_1_0 := (_object_w66 (M := M));
            let _wd_1_1 := _object_w324;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
              let _atomic_wd_1_0 := (_object_w66 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_202605 (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (let _wd_1_0 := (_object_w66 (M := M));
            let _wd_1_1 := _object_w320;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w320
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := (_object_w66 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w320
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w320
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ))))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_202608; exact (M.real_members (Litex.denote (let _wd_1_0 := (_object_w66 (M := M));
            let _wd_1_1 := _object_w320;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w320
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := (_object_w66 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w320
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w320
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ))))))).mpr ⟨_litex_real, _litex_value⟩) h_202608)
            )
          )
      )

    have h_203647 : Litex.In (let _wd_1_0 := (_object_w66 (M := M));
    let _wd_1_1 := _object_w320;
    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w320
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      ))) (by
      let _atomic_wd_1_0 := (_object_w66 (M := M))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
      let _atomic_wd_1_0 := _object_w320
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w320
      exact (by
        let _litex_power := _atomic_wd_1_0
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      ))))) (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_203153 : (by
              let _atomic_wd_1_1 := (let _wd_1_0 := (_object_w66 (M := M));
              let _wd_1_1 := _object_w324;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_2_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                let _atomic_wd_2_0 := (_object_w66 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_2_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_2_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))))
              exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
              let _atomic_wd_1_1 := (let _wd_1_0 := (_object_w66 (M := M));
              let _wd_1_1 := _object_w324;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_2_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                let _atomic_wd_2_0 := (_object_w66 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_2_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_2_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))))
              exact (Litex.powStructuralPositiveOfPositive _atomic_wd_1_1 (by
                let _atomic_wd_2_1 := (_object_w66 (M := M))
                exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                  let _atomic_wd_3_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).mpr (by
                  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                    apply Complex.ofReal_injective
                    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                  have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_2_1 (by
                  let _atomic_wd_3_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (4 : ℝ)) := by
                    apply Complex.ofReal_injective
                    exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_1 (by
                  let _atomic_wd_3_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
              have h_203582 : (by
              let _atomic_wd_1_0 := _object_w324
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) := (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_w321 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (((h_198190).symm).trans h_198192) (show @Eq M.Value _ _ from Eq.refl _) h_201220)))
              exact Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
            let _wd_1_1 := _object_w324;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
              let _atomic_wd_1_0 := (_object_w66 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (let _wd_1_0 := (_object_w66 (M := M));
            let _wd_1_1 := _object_w320;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w320
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ))) (by
              let _atomic_wd_1_0 := (_object_w66 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w320
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              )) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w320
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ))))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Eq.symm h_202605) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (let _wd_1_0 := (_object_w66 (M := M));
            let _wd_1_1 := _object_w324;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
              let _atomic_wd_1_0 := (_object_w66 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_203153; exact (M.real_members (Litex.denote (let _wd_1_0 := (_object_w66 (M := M));
            let _wd_1_1 := _object_w324;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
              let _atomic_wd_1_0 := (_object_w66 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))))).mpr ⟨_litex_real, _litex_value⟩) h_203153)
            )
          )
      )

    have h_202606 :=
      h_202603

    have h_204185 : Litex.In (let _wd_1_0 := _object_i36;
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _object_i36
      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_203648 : (by
              let _atomic_wd_1_1 := (let _wd_1_0 := (_object_w66 (M := M));
              let _wd_1_1 := _object_w324;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_2_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                let _atomic_wd_2_0 := (_object_w66 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_2_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_2_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))))
              exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
              let _atomic_wd_1_1 := (let _wd_1_0 := (_object_w66 (M := M));
              let _wd_1_1 := _object_w324;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_2_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                let _atomic_wd_2_0 := (_object_w66 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_2_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_2_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))))
              exact (Litex.powStructuralPositiveOfPositive _atomic_wd_1_1 (by
                let _atomic_wd_2_1 := (_object_w66 (M := M))
                exact ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                  let _atomic_wd_3_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).mpr (by
                  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                    apply Complex.ofReal_injective
                    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                  have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_2_1 (by
                  let _atomic_wd_3_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (4 : ℝ)) := by
                    apply Complex.ofReal_injective
                    exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_1 (by
                  let _atomic_wd_3_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num))))
                  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
              have h_204116 : (by
              let _atomic_wd_1_0 := _object_w324
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) := (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_w321 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (((h_198190).symm).trans h_198192) (show @Eq M.Value _ _ from Eq.refl _) h_201220)))
              exact Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
            let _wd_1_1 := _object_w324;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
              let _atomic_wd_1_0 := (_object_w66 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (let _wd_1_0 := _object_i36;
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_i36
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_202606 (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (let _wd_1_0 := (_object_w66 (M := M));
            let _wd_1_1 := _object_w324;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
              let _atomic_wd_1_0 := (_object_w66 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_203648; exact (M.real_members (Litex.denote (let _wd_1_0 := (_object_w66 (M := M));
            let _wd_1_1 := _object_w324;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
              let _atomic_wd_1_0 := (_object_w66 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))))).mpr ⟨_litex_real, _litex_value⟩) h_203648)
            )
          )
      )

    have h_204623 : Litex.In (let _wd_1_0 := (_object_w66 (M := M));
    let _wd_1_1 := _object_w324;
    (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w324
      exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
        let _litex_power := (_object_w324).val.left
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_198733
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
      let _atomic_wd_1_0 := (_object_w66 (M := M))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
      let _atomic_wd_1_0 := _object_w324
      exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
        let _litex_power := (_object_w324).val.left
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_198733
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w324
      exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
        let _litex_power := (_object_w324).val.left
        have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        have _elaborated_power_exponent := h_198733
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
      ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_204186 : (by
              let _atomic_wd_1_1 := (let _wd_1_0 := _object_i36;
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                let _atomic_wd_2_0 := _object_i36
                exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.inOfSame _object_i36 _atomic_wd_2_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
              let _atomic_wd_1_1 := (let _wd_1_0 := _object_i36;
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                let _atomic_wd_2_0 := _object_i36
                exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.inOfSame _object_i36 _atomic_wd_2_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              exact (Litex.powStructuralPositiveOfEven _atomic_wd_1_1 (by
                let _atomic_wd_2_0 := _object_i36
                exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.inOfSame _object_i36 _atomic_wd_2_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num) (by norm_num) (by
                let _atomic_wd_2_0 := _object_i36
                exact (Litex.notSameOfSame _object_i36 _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199623))))
              have h_204592 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
              exact Litex.inOfSame (let _wd_1_0 := _object_i36;
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_i36
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (let _wd_1_0 := (_object_w66 (M := M));
            let _wd_1_1 := _object_w324;
            (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
              let _atomic_wd_1_0 := (_object_w66 (M := M))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
              let _atomic_wd_1_0 := _object_w324
              exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                let _litex_power := (_object_w324).val.left
                have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                have _elaborated_power_exponent := h_198733
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
              ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Eq.symm h_202606) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (let _wd_1_0 := _object_i36;
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_i36
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_204186; exact (M.real_members (Litex.denote (let _wd_1_0 := _object_i36;
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_i36
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))).mpr ⟨_litex_real, _litex_value⟩) h_204186)
            )
          )
      )

    have h_202607 :=
      h_202604

    have h_205092 : Litex.In (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_204624 : (by
              let _atomic_wd_1_1 := (let _wd_1_0 := _object_i36;
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                let _atomic_wd_2_0 := _object_i36
                exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.inOfSame _object_i36 _atomic_wd_2_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
              let _atomic_wd_1_1 := (let _wd_1_0 := _object_i36;
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                let _atomic_wd_2_0 := _object_i36
                exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.inOfSame _object_i36 _atomic_wd_2_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              exact (Litex.powStructuralPositiveOfEven _atomic_wd_1_1 (by
                let _atomic_wd_2_0 := _object_i36
                exact (Litex.inRPos_real _atomic_wd_2_0 (Litex.inOfSame _object_i36 _atomic_wd_2_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num) (by norm_num) (by
                let _atomic_wd_2_0 := _object_i36
                exact (Litex.notSameOfSame _object_i36 _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199623))))
              have h_205059 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
              exact Litex.inOfSame (let _wd_1_0 := _object_i36;
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_i36
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_202607 (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (let _wd_1_0 := _object_i36;
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_i36
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_204624; exact (M.real_members (Litex.denote (let _wd_1_0 := _object_i36;
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_i36
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))).mpr ⟨_litex_real, _litex_value⟩) h_204624)
            )
          )
      )

    have h_205592 : Litex.In (let _wd_1_0 := _object_i36;
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _object_i36
      exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.RPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_205093 : (by
              let _atomic_wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
              exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
              let _atomic_wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
              exact (Litex.powStructuralPositiveOfEven _atomic_wd_1_1 (Litex.inRPos_real _object_i36 h_199620) (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num) (by norm_num) h_199623))
              have h_205557 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
              exact Litex.inOfSame (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (let _wd_1_0 := _object_i36;
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _object_i36
              exact (Litex.inRPos_real _atomic_wd_1_0 (Litex.inOfSame _object_i36 _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_199624 (show @Eq M.Value _ _ from Eq.refl _) h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Eq.symm h_202607) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_205093; exact (M.real_members (Litex.denote (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))).mpr ⟨_litex_real, _litex_value⟩) h_205093)
            )
          )
      )

    have h_205593 :=
      (Eq.trans h_202602 h_202603)

    have h_205594 :=
      (Eq.trans (Eq.trans h_202602 h_202603) h_202604)

    have h_205595 :=
      (Eq.trans h_202603 h_202604)
    have h_198194 : (by
      let _chain_wd_198194_0 := (let _object_w325 := (_object_w320).val.exponent;
      (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w325 (h_20132 (M := M)) (by
        let _atomic_wd_1_0 := _object_w325
        exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
      let _chain_wd_198194_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
      let _wd_1_1 := (let _wd_2_0 := (_object_w66 (M := M));
      let _wd_2_1 := _object_w320;
      (Litex.powNatReal _wd_2_0 _wd_2_1 (Litex.NativeBridge.asNat _wd_2_1 (by
        let _atomic_wd_1_0 := _object_w320
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
          have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
        ))) (by
        let _atomic_wd_1_0 := (_object_w66 (M := M))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
        let _atomic_wd_1_0 := _object_w320
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
          have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
        )) (Litex.NativeBridge.asNat_spec _wd_2_1 (by
        let _atomic_wd_1_0 := _object_w320
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
          have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
        )))));
      (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _atomic_wd_1_0 := _wd_1_1
        exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
        let _wd_1_1 := _object_w324;
        (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
          let _atomic_wd_1_0 := (_object_w66 (M := M))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (h_202602).symm (show @Eq M.Value _ _ from Eq.refl _) h_203152)))))
      let _chain_wd_198194_2 := _chain_wd_198194_1
      let _chain_wd_198194_3 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
      let _wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
      (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _atomic_wd_1_0 := _wd_1_1
        exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
        let _wd_1_1 := _object_w324;
        (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
          let _atomic_wd_1_0 := (_object_w66 (M := M))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_205595 (show @Eq M.Value _ _ from Eq.refl _) h_203152)))))
      exact ((by
        let _equal_wd_1_0 := _chain_wd_198194_0
        let _equal_wd_1_1 := _chain_wd_198194_1
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
        let _equal_wd_1_0 := _chain_wd_198194_2
        let _equal_wd_1_1 := _chain_wd_198194_3
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _chain_wd_198194_0 := (let _object_w325 := (_object_w320).val.exponent;
              (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w325 (h_20132 (M := M)) (by
                let _atomic_wd_1_0 := _object_w325
                exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
              let _chain_wd_198194_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
              let _wd_1_1 := (let _wd_2_0 := (_object_w66 (M := M));
              let _wd_2_1 := _object_w320;
              (Litex.powNatReal _wd_2_0 _wd_2_1 (Litex.NativeBridge.asNat _wd_2_1 (by
                let _atomic_wd_1_0 := _object_w320
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ))) (by
                let _atomic_wd_1_0 := (_object_w66 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_1_0 := _object_w320
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                )) (Litex.NativeBridge.asNat_spec _wd_2_1 (by
                let _atomic_wd_1_0 := _object_w320
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                )))));
              (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _atomic_wd_1_0 := _wd_1_1
                exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
                let _wd_1_1 := _object_w324;
                (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                  let _atomic_wd_1_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) (h_202602).symm (show @Eq M.Value _ _ from Eq.refl _) h_203152)))))
              let _chain_wd_198194_2 := _chain_wd_198194_1
              let _chain_wd_198194_3 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
              let _wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
              (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _atomic_wd_1_0 := _wd_1_1
                exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
                let _wd_1_1 := _object_w324;
                (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                  let _atomic_wd_1_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_205595 (show @Eq M.Value _ _ from Eq.refl _) h_203152)))))
              exact (And.intro (let _equal_wd_1_0 := _chain_wd_198194_0;
              let _equal_wd_1_1 := _chain_wd_198194_1;
              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))))) from by
                have _litex_residual : (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))))) := (show @Eq M.Value _ _ from Eq.refl _)
                exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))))).trans (by
                let _litex_original := _equal_wd_1_0
                let _litex_literal := (let _wd_1_0 := (_object_i15 (M := M));
                let _object_w333 := (_equal_wd_1_0).val.argument;
                (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _wd_1_0 _object_w333 (Litex.formulaFnInFnSet _wd_1_0) (by
                  let _atomic_wd_1_0 := _object_w333
                  exact (Litex.addInN _value_i35 (Litex.number (M := M) (1 : ℂ)) h_198733 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_20133 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ)))))) from rfl))
              ))).trans _litex_residual))) (congrArg₂ M.mulValue (show (M.number (4 : ℂ)) = (M.number (4 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)) (show (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.addValue (Litex.denote _value_i35) (M.number (1 : ℂ))))) = (M.powValue (Litex.denote _object_i36) (M.number (2 : ℂ))) from h_205594))))
          )
      )

    have h_211901 :=
      (And.left h_198194)

    have h_211902 :=
      (And.right h_198194)

    have h_211903 :=
      h_211901

    have h_211904 :=
      h_211902

    have h_211905 :=
      (Eq.trans h_211901 h_211902)
    have h_198195 : (by
      let _chain_wd_198195_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_198733 True.intro);
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
      let _chain_wd_198195_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_199620));
      let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
        let _atomic_wd_1_0 := _wd_2_0
        exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (Litex.inRPos_real _object_i36 h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
      let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
      (Litex.div _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.mulInC _wd_1_1 _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_199620))
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
        )) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      let _chain_wd_198195_2 := _chain_wd_198195_1
      let _chain_wd_198195_3 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (16 : ℂ));
      let _wd_2_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
      (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (16 : ℂ)) (by
        let _atomic_wd_1_0 := _wd_2_1
        exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
        let _wd_1_1 := _object_w324;
        (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
          let _atomic_wd_1_0 := (_object_w66 (M := M))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_205595 (show @Eq M.Value _ _ from Eq.refl _) h_203152)))));
      let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
      (Litex.div _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.mulInC (Litex.number (M := M) (16 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (16 : ℂ)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
        let _wd_1_1 := _object_w324;
        (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
          let _atomic_wd_1_0 := (_object_w66 (M := M))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (_atomic_wd_1_0).val.right (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_205595 (show @Eq M.Value _ _ from Eq.refl _) h_203152)))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      let _chain_wd_198195_4 := _chain_wd_198195_3
      let _chain_wd_198195_5 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
      let _wd_1_1 := ((_chain_wd_198195_4).val.left).val.right;
      (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
        let _atomic_wd_1_0 := _wd_1_1
        exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
        let _wd_1_1 := _object_w324;
        (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
          let _atomic_wd_1_0 := (_object_w66 (M := M))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
          let _atomic_wd_1_0 := _object_w324
          exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
            let _litex_power := (_object_w324).val.left
            have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
            have _elaborated_power_exponent := h_198733
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
          ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_205595 (show @Eq M.Value _ _ from Eq.refl _) h_203152)))))
      exact ((by
        let _equal_wd_1_0 := _chain_wd_198195_0
        let _equal_wd_1_1 := _chain_wd_198195_1
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
        let _equal_wd_1_0 := _chain_wd_198195_2
        let _equal_wd_1_1 := _chain_wd_198195_3
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
        let _equal_wd_1_0 := _chain_wd_198195_4
        let _equal_wd_1_1 := _chain_wd_198195_5
        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _chain_wd_198195_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i35 (h_20132 (M := M)) h_198733 True.intro);
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
              let _chain_wd_198195_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_199620));
              let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                let _atomic_wd_1_0 := _wd_2_0
                exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (Litex.inRPos_real _object_i36 h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
              let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
              (Litex.div _wd_1_0 _wd_1_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.mulInC _wd_1_1 _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_199620))
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                )) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
              let _chain_wd_198195_2 := _chain_wd_198195_1
              let _chain_wd_198195_3 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (16 : ℂ));
              let _wd_2_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
              (Litex.mul _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (16 : ℂ)) (by
                let _atomic_wd_1_0 := _wd_2_1
                exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
                let _wd_1_1 := _object_w324;
                (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                  let _atomic_wd_1_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_205595 (show @Eq M.Value _ _ from Eq.refl _) h_203152)))));
              let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
              (Litex.div _wd_1_0 _wd_1_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (Litex.mulInC (Litex.number (M := M) (16 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (16 : ℂ)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
                let _wd_1_1 := _object_w324;
                (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                  let _atomic_wd_1_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (_atomic_wd_1_0).val.right (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_205595 (show @Eq M.Value _ _ from Eq.refl _) h_203152)))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
              let _chain_wd_198195_4 := _chain_wd_198195_3
              let _chain_wd_198195_5 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
              let _wd_1_1 := ((_chain_wd_198195_4).val.left).val.right;
              (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                let _atomic_wd_1_0 := _wd_1_1
                exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
                let _wd_1_1 := _object_w324;
                (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                  let _atomic_wd_1_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_205595 (show @Eq M.Value _ _ from Eq.refl _) h_203152)))))
              exact (And.intro (congrArg₂ M.divValue (show (M.powValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (Litex.denote _value_i35)) (M.number (2 : ℂ))) = (M.powValue (M.mulValue (M.number (4 : ℂ)) (Litex.denote _object_i36)) (M.number (2 : ℂ))) from (congrArg₂ M.powValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (Litex.denote _value_i35)) = (M.mulValue (M.number (4 : ℂ)) (Litex.denote _object_i36)) from h_200545) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.number (4 : ℂ)) = (M.number (4 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _))) (And.intro (let _equal_wd_1_0 := _chain_wd_198195_2;
              let _equal_wd_1_1 := _chain_wd_198195_3;
              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (congrArg₂ M.divValue (show (M.powValue (M.mulValue (M.number (4 : ℂ)) (Litex.denote _object_i36)) (M.number (2 : ℂ))) = (M.mulValue (M.number (16 : ℂ)) (M.powValue (Litex.denote _object_i36) (M.number (2 : ℂ)))) from (let _equal_wd_2_0 := (_equal_wd_1_0).val.left;
              let _equal_wd_2_1 := (_equal_wd_1_1).val.left;
              (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((4 : ℂ) * (Litex.NativeBridge.asComplex _object_i36 (Litex.positiveRealToComplex _object_i36 h_199620))) ^ (2 : ℕ)) ((16 : ℂ) * ((Litex.NativeBridge.asComplex _object_i36 (Litex.positiveRealToComplex _object_i36 h_199620)) ^ (2 : ℕ))) (Litex.NativeBridge.denotePowNatReal (_equal_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                let _atomic_wd_1_0 := (_equal_wd_2_0).val.base
                exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (Litex.inRPos_real _object_i36 h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) _object_i36 ((_equal_wd_2_0).val.base).wd.1 ((_equal_wd_2_0).val.base).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.asComplex_spec _object_i36 (Litex.positiveRealToComplex _object_i36 h_199620)))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (16 : ℂ)) (_equal_wd_2_1).val.right (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ)) (Litex.NativeBridge.denotePowNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _object_i36 (Litex.positiveRealToComplex _object_i36 h_199620)))) (by ring!))))) (show (M.number (4 : ℂ)) = (M.number (4 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _))))) (let _equal_wd_1_0 := _chain_wd_198195_4;
              let _equal_wd_1_1 := _chain_wd_198195_5;
              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((16 : ℂ) * ((Litex.NativeBridge.asComplex _object_i36 (Litex.positiveRealToComplex _object_i36 h_199620)) ^ (2 : ℕ))) / (4 : ℂ)) ((4 : ℂ) * ((Litex.NativeBridge.asComplex _object_i36 (Litex.positiveRealToComplex _object_i36 h_199620)) ^ (2 : ℕ))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_0).val.left (Litex.number (M := M) (4 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteMul (Litex.number (M := M) (16 : ℂ)) ((_equal_wd_1_0).val.left).val.right ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ)) (Litex.NativeBridge.denotePowNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _object_i36 (Litex.positiveRealToComplex _object_i36 h_199620)))) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denotePowNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _object_i36 (Litex.positiveRealToComplex _object_i36 h_199620)))) (by
                have _litex_nz_0 : ((4 : ℂ) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (Litex.number (M := M) (4 : ℂ)) (4 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
                litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
              )))))))
          )
      )

    have h_259177 :=
      (And.left h_198195)

    have h_259178 :=
      (And.left (And.right h_198195))

    have h_259179 :=
      (And.right (And.right h_198195))

    have h_259180 :=
      h_259177

    have h_259181 :=
      h_259178

    have h_261142 : Litex.Same (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_199620));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (Litex.inRPos_real _object_i36 h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (let _wd_1_0 := (Litex.number (M := M) (16 : ℂ));
    let _wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (16 : ℂ)) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
      let _wd_1_1 := _object_w324;
      (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
        let _atomic_wd_1_0 := _object_w324
        exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
          let _litex_power := (_object_w324).val.left
          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
          have _elaborated_power_exponent := h_198733
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
        let _atomic_wd_1_0 := (_object_w66 (M := M))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
        let _atomic_wd_1_0 := _object_w324
        exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
          let _litex_power := (_object_w324).val.left
          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
          have _elaborated_power_exponent := h_198733
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
        let _atomic_wd_1_0 := _object_w324
        exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
          let _litex_power := (_object_w324).val.left
          have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
          have _elaborated_power_exponent := h_198733
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
        ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_205595 (show @Eq M.Value _ _ from Eq.refl _) h_203152))))) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.divCancelCommonDenominator (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_199620));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (Litex.inRPos_real _object_i36 h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (let _wd_1_0 := (Litex.number (M := M) (16 : ℂ));
            let _wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (16 : ℂ)) (by
              let _atomic_wd_1_0 := _wd_1_1
              exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
              let _wd_1_1 := _object_w324;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                let _atomic_wd_1_0 := (_object_w66 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_1_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_1_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_205595 (show @Eq M.Value _ _ from Eq.refl _) h_203152))))) (Litex.number (M := M) (4 : ℂ)) (by
              let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_199620));
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                let _atomic_wd_2_0 := _wd_1_0
                exact (Litex.mulInR (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) (Litex.inRPos_real _object_i36 h_199620))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              exact (by
                let _litex_power := _atomic_wd_1_0
                have _elaborated_power_base := (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) _object_i36 (Litex.numberInC (M := M) (4 : ℂ)) (Litex.positiveRealToComplex _object_i36 h_199620))
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
              )) (by
              let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (16 : ℂ));
              let _wd_1_1 := (Litex.powNatReal _object_i36 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inRPos_real _object_i36 h_199620) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
              (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (16 : ℂ)) (by
                let _atomic_wd_2_0 := _wd_1_1
                exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
                let _wd_1_1 := _object_w324;
                (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                  let _atomic_wd_1_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                  let _atomic_wd_1_0 := _object_w324
                  exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                    let _litex_power := (_object_w324).val.left
                    have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                    have _elaborated_power_exponent := h_198733
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                  ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) _atomic_wd_2_0 (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_205595 (show @Eq M.Value _ _ from Eq.refl _) h_203152)))))
              exact (Litex.mulInC (Litex.number (M := M) (16 : ℂ)) (_atomic_wd_1_0).val.right (Litex.numberInC (M := M) (16 : ℂ)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.inOfSame (let _wd_1_0 := (_object_w66 (M := M));
              let _wd_1_1 := _object_w324;
              (Litex.powNatReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.asNat _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (by
                let _atomic_wd_1_0 := (_object_w66 (M := M))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                let _atomic_wd_1_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.NativeBridge.asNat_spec _wd_1_1 (by
                let _atomic_wd_1_0 := _object_w324
                exact (Litex.mulInN (_object_w324).val.left (Litex.number (M := M) (2 : ℂ)) (by
                  let _litex_power := (_object_w324).val.left
                  have _elaborated_power_base := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  have _elaborated_power_exponent := h_198733
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
                ) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))) (_atomic_wd_1_0).val.right (Litex.RPos (M := M)) (Litex.RPos (M := M)) h_205595 (show @Eq M.Value _ _ from Eq.refl _) h_203152)))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_259181)
          )
      )

    have h_259182 :=
      h_259179

    have h_261143 :=
      (Eq.trans h_259177 h_259178)

    have h_261144 :=
      (Eq.trans (Eq.trans h_259177 h_259178) h_259179)

    have h_261145 :=
      (Eq.trans h_259178 h_259179)
    exact ((h_211905).trans (h_261144).symm)
  )

theorem h_263051 : ∀ {_Host_i38 : Type v38} [_rep_i38 : Litex.Representation M _Host_i38] (_value_i38 : Litex.Obj (M := M) _Host_i38) (h_263084 : Litex.In _value_i38 (Litex.N (M := M))), (by
  let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i38 (h_10610 (M := M)) h_263084 True.intro)
  let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i38 (h_20132 (M := M)) h_263084 True.intro)
  exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    intro _Host_i38 _rep_i38 _value_i38 h_263084
    have h_263085 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i38 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i38 h_263084)
          )
      )
    have h_263354 : Litex.In _value_i38 (Litex.N (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_263084
          )
      )
    have h_263355 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i38 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i38 h_263354)
          )
      )
    have h_304775 : ∀ (_raw_i39 : M.Value) (h_263369 : M.mem _raw_i39 (M.standard .integer)) (h_263370 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i39 = M.number (_s : ℂ) ∧ _r ≤ _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) _raw_i39) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) _raw_i39) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
      (by
        litex_checked_step =>
          exact (
            (by
              intro _raw_i39 h_263369 h_263370
              let _value_i39 := Litex.semanticObject (M := M) _raw_i39 (M.member_isSet h_263369)
              have h_263421 : Litex.In _value_i39 (Litex.N (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i39 h_263369 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                        have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                        have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                          apply Complex.ofReal_injective
                          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_263370)
                    )
                )
              exact Litex.integerInductionFromZero (fun (_raw_i39 : M.Value) => (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) _raw_i39) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) _raw_i39) = M.number (_s : ℂ) ∧ _r ≤ _s)) (by
                let _raw_i39 : M.Value := M.number 0
                have h_263818 : M.mem _raw_i39 (M.standard .integer) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num))
                let _value_i39 := Litex.semanticObject (M := M) _raw_i39 (M.member_isSet h_263818)
                have h_263818 : Litex.In _value_i39 (Litex.Z (M := M)) := h_263818
                have h_263819 : Litex.Same _value_i39 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by rfl)
                      )
                  )
                let _object_w343 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_10028 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)

                have h_263053 : (by
                  let _equal_wd_1_0 := _object_w343
                  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := _object_w343;
                        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (by
                          let _checked_call := _equal_wd_1_0
                          have _checked_case_guard : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
                          have _selected_beta := (h_10030 (M := M)) _checked_call.val.argument _checked_call.wd.2.1 _checked_case_guard
                          exact _selected_beta.trans (show @Eq M.Value _ _ from Eq.refl _))))
                      )
                  )
                let _object_w345 := (let _wd_1_0 := _object_w343;
                (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _wd_1_0 (h_96 (M := M)) (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.inRPos_real _object_w343 (Litex.callInOutput _object_w343))) True.intro))

                have h_263054 : (by
                  let _equal_wd_1_0 := _object_w345
                  let _equal_wd_1_1 := (_object_w63 (M := M))
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_263053)
                      )
                  )
                have h_263055 : (by
                  let _equal_wd_1_0 := (_object_w63 (M := M))
                  let _equal_wd_1_1 := (_object_w64 (M := M))
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (h_21882 (M := M))
                      )
                  )
                have h_263056 : (by
                  let _equal_wd_1_0 := _object_w345
                  let _equal_wd_1_1 := (_object_w64 (M := M))
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        ((h_263054).trans h_263055)
                      )
                  )
                let _object_w346 := (let _wd_1_0 := _object_w345;
                (Litex.abs _wd_1_0 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (by
                    let _litex_return_call := _object_w345
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))

                let _object_w347 := (let _wd_1_0 := (_object_w64 (M := M));
                (Litex.abs _wd_1_0 (by
                  let _atomic_wd_1_0 := (_object_w64 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_object_w64 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))))

                have h_263057 : (by
                  let _equal_wd_1_0 := _object_w346
                  let _equal_wd_1_1 := _object_w347
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (congrArg (Litex.absValue (M := M)) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ)))) = (M.negValue (M.number (1 : ℂ))) from h_263056))
                      )
                  )
                have h_263058 : (by
                  let _equal_wd_1_0 := _object_w347
                  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := _object_w347;
                        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((|(-1 : ℝ)| : ℝ) : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteAbs (_object_w347).val.arg (_object_w347).wd (-1 : ℝ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_object_w64 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (((-1 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
                      )
                  )
                have h_263059 : (by
                  let _chain_wd_263059_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)
                  let _chain_wd_263059_1 := _object_w346
                  let _chain_wd_263059_2 := _chain_wd_263059_1
                  let _chain_wd_263059_3 := _object_w347
                  let _chain_wd_263059_4 := _chain_wd_263059_3
                  exact ((by
                    let _equal_wd_1_0 := _chain_wd_263059_0
                    let _equal_wd_1_1 := _chain_wd_263059_1
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
                    let _equal_wd_1_0 := _chain_wd_263059_2
                    let _equal_wd_1_1 := _chain_wd_263059_3
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
                    let _equal_wd_1_0 := _chain_wd_263059_4
                    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _chain_wd_263059_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)
                          let _chain_wd_263059_1 := _object_w346
                          let _chain_wd_263059_2 := _chain_wd_263059_1
                          let _chain_wd_263059_3 := _object_w347
                          let _chain_wd_263059_4 := _chain_wd_263059_3
                          exact (And.intro (let _equal_wd_1_0 := _chain_wd_263059_0;
                          let _equal_wd_1_1 := _chain_wd_263059_1;
                          (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.number (0 : ℂ))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ))))) from by
                            have _litex_residual : (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ))))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ))))) := (show @Eq M.Value _ _ from Eq.refl _)
                            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (M.number (0 : ℂ))))).trans (by
                            let _litex_original := _equal_wd_1_0
                            let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
                            let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                            (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro))
                            have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_10611 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                            have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (Litex.denote _litex_literal.val.argument) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ))))) from rfl))
                          ))).trans _litex_residual))) (And.intro h_263057 h_263058)))
                      )
                  )

                have h_264493 :=
                  (And.left h_263059)

                have h_264494 :=
                  (And.left (And.right h_263059))

                have h_264495 :=
                  (And.right (And.right h_263059))

                have h_264496 :=
                  h_264493

                have h_264497 :=
                  h_264494

                have h_264498 :=
                  h_264495

                have h_264499 :=
                  (Eq.trans h_264493 h_264494)

                have h_264500 :=
                  (Eq.trans (Eq.trans h_264493 h_264494) h_264495)

                have h_264501 :=
                  (Eq.trans h_264494 h_264495)
                have h_263060 : (by
                  let _chain_wd_263060_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)
                  let _chain_wd_263060_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
                  let _wd_1_1 := (let _wd_2_0 := (_object_w66 (M := M));
                  let _wd_2_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)));
                  (Litex.powNatReal _wd_2_0 _wd_2_1 (1 : ℕ) (by
                    let _atomic_wd_1_0 := (_object_w66 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_2_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num))));
                  (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (_atomic_wd_1_0).val.exponent (1 : ℕ) (by
                      let _atomic_wd_2_0 := (_object_w66 (M := M))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.exponent
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber (_atomic_wd_1_0).val.exponent (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))).trans (congrArg M.number (by norm_num : (((1 : ℂ) / (4 : ℂ)) ^ (1 : ℕ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ)))))))
                  let _chain_wd_263060_2 := _chain_wd_263060_1
                  let _chain_wd_263060_3 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
                  let _wd_1_1 := (_object_w66 (M := M));
                  (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                    let _atomic_wd_1_0 := (_object_w66 (M := M))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (4 : ℂ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ)))))))
                  let _chain_wd_263060_4 := _chain_wd_263060_3
                  exact ((by
                    let _equal_wd_1_0 := _chain_wd_263060_0
                    let _equal_wd_1_1 := _chain_wd_263060_1
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((by
                    let _equal_wd_1_0 := _chain_wd_263060_2
                    let _equal_wd_1_1 := _chain_wd_263060_3
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
                    let _equal_wd_1_0 := _chain_wd_263060_4
                    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _chain_wd_263060_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)
                          let _chain_wd_263060_1 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
                          let _wd_1_1 := (let _wd_2_0 := (_object_w66 (M := M));
                          let _wd_2_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)));
                          (Litex.powNatReal _wd_2_0 _wd_2_1 (1 : ℕ) (by
                            let _atomic_wd_1_0 := (_object_w66 (M := M))
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                            let _atomic_wd_1_0 := _wd_2_1
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num))));
                          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                            let _atomic_wd_1_0 := _wd_1_1
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (_atomic_wd_1_0).val.exponent (1 : ℕ) (by
                              let _atomic_wd_2_0 := (_object_w66 (M := M))
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                              let _atomic_wd_2_0 := (_atomic_wd_1_0).val.exponent
                              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber (_atomic_wd_1_0).val.exponent (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))).trans (congrArg M.number (by norm_num : (((1 : ℂ) / (4 : ℂ)) ^ (1 : ℕ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ)))))))
                          let _chain_wd_263060_2 := _chain_wd_263060_1
                          let _chain_wd_263060_3 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
                          let _wd_1_1 := (_object_w66 (M := M));
                          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
                            let _atomic_wd_1_0 := (_object_w66 (M := M))
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (4 : ℂ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ)))))))
                          let _chain_wd_263060_4 := _chain_wd_263060_3
                          exact (And.intro (let _equal_wd_1_0 := _chain_wd_263060_0;
                          let _equal_wd_1_1 := _chain_wd_263060_1;
                          (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.number (0 : ℂ))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (0 : ℂ))))) from by
                            have _litex_residual : (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (0 : ℂ))))) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (0 : ℂ))))) := (show @Eq M.Value _ _ from Eq.refl _)
                            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.number (0 : ℂ))))).trans (by
                            let _litex_original := _equal_wd_1_0
                            let _litex_literal := (let _wd_1_0 := (_object_i15 (M := M));
                            let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                            (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro))
                            have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_20133 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                            have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (0 : ℂ))))) from rfl))
                          ))).trans _litex_residual))) (And.intro (let _equal_wd_1_0 := _chain_wd_263060_2;
                          let _equal_wd_1_1 := _chain_wd_263060_3;
                          (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((4 : ℂ) * (((1 : ℂ) / (4 : ℂ)) ^ (1 : ℕ))) ((4 : ℂ) * ((1 : ℂ) / (4 : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.right).val.base ((_equal_wd_1_0).val.right).val.exponent (1 : ℕ) (by
                            let _atomic_wd_1_0 := (_object_w66 (M := M))
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                            let _atomic_wd_1_0 := ((_equal_wd_1_0).val.right).val.exponent
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber ((_equal_wd_1_0).val.right).val.exponent (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))) (by norm_num)))) (let _equal_wd_1_0 := _chain_wd_263060_4;
                          (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((4 : ℂ) * ((1 : ℂ) / (4 : ℂ))) (1 : ℂ) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))))))
                      )
                  )

                have h_266329 :=
                  (And.left h_263060)

                have h_266330 :=
                  (And.left (And.right h_263060))

                have h_266331 :=
                  (And.right (And.right h_263060))

                have h_266332 :=
                  h_266329

                have h_266333 :=
                  h_266330

                have h_266475 : Litex.Same (let _wd_1_0 := (_object_w66 (M := M));
                let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)));
                (Litex.powNatReal _wd_1_0 _wd_1_1 (1 : ℕ) (by
                  let _atomic_wd_1_0 := (_object_w66 (M := M))
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                  let _atomic_wd_1_0 := _wd_1_1
                  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)))) (_object_w66 (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.mulCancelLeftLeft (let _wd_1_0 := (_object_w66 (M := M));
                        let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)));
                        (Litex.powNatReal _wd_1_0 _wd_1_1 (1 : ℕ) (by
                          let _atomic_wd_1_0 := (_object_w66 (M := M))
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                          let _atomic_wd_1_0 := _wd_1_1
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)))) (_object_w66 (M := M)) (Litex.number (M := M) (4 : ℂ)) (by
                          let _atomic_wd_1_0 := (let _wd_1_0 := (_object_w66 (M := M));
                          let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)));
                          (Litex.powNatReal _wd_1_0 _wd_1_1 (1 : ℕ) (by
                            let _atomic_wd_2_0 := (_object_w66 (M := M))
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                            let _atomic_wd_2_0 := _wd_1_1
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num))))
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (_atomic_wd_1_0).val.exponent (1 : ℕ) (by
                            let _atomic_wd_2_0 := (_object_w66 (M := M))
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
                            let _atomic_wd_2_0 := (_atomic_wd_1_0).val.exponent
                            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (0 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (0 : ℕ)) (1 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber (_atomic_wd_1_0).val.exponent (Litex.number (M := M) ((1 : ℕ) : ℂ)) ((2 : ℂ) ^ (0 : ℕ)) ((1 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((0 : ℕ) : ℂ)) (0 : ℂ) ((0 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((0 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((1 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))).trans (congrArg M.number (by norm_num : (((1 : ℂ) / (4 : ℂ)) ^ (1 : ℕ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ))))) (by
                          let _atomic_wd_1_0 := (_object_w66 (M := M))
                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (4 : ℂ)) = ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (4 : ℂ))))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_266333)
                      )
                  )

                have h_266334 :=
                  h_266331

                have h_266476 :=
                  (Eq.trans h_266329 h_266330)

                have h_266477 :=
                  (Eq.trans (Eq.trans h_266329 h_266330) h_266331)

                have h_266478 :=
                  (Eq.trans h_266330 h_266331)
                show (fun (_raw_i39 : M.Value) => (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) _raw_i39) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) _raw_i39) = M.number (_s : ℂ) ∧ _r ≤ _s)) (M.number 0)
                exact (by
                  let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)
                  let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) True.intro)
                  exact (Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1 (h_264500).symm (h_266477).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
              ) (by
                intro _raw_i39 _induction_integer _induction_nonnegative _induction_hypothesis
                have h_270328 : M.mem _raw_i39 (M.standard .integer) := _induction_integer
                let _value_i39 := Litex.semanticObject (M := M) _raw_i39 (M.member_isSet h_270328)
                have h_270328 : Litex.In _value_i39 (Litex.Z (M := M)) := h_270328
                have h_270329 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i39 :=
                  (by
                    litex_checked_step =>
                      exact (
                        _induction_nonnegative
                      )
                  )
                have h_270380 : Litex.In _value_i39 (Litex.N (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i39 h_270328 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_270329)
                      )
                  )
                have h_263052 : Litex.Le (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro) :=
                  (by
                    litex_checked_step =>
                      exact (
                        _induction_hypothesis
                      )
                  )
                let _object_w358 := (let _wd_1_0 := (let _object_w352 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => True) (_object_i8 (M := M)) _value_i39 (h_10028 (M := M)) h_270380 True.intro);
                (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w352 (h_96 (M := M)) (by
                  let _atomic_wd_1_0 := _object_w352
                  exact (Litex.inRPos_real _object_w352 (Litex.callInOutput _object_w352))) True.intro));
                (Litex.abs _wd_1_0 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (by
                    let _litex_return_call := _atomic_wd_1_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))

                have h_263061 : (by
                  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                  let _equal_wd_1_1 := _object_w358
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                        let _equal_wd_1_1 := _object_w358;
                        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i39)) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i39)))) from by
                          have _litex_residual : (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i39)))) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i39)))) := (show @Eq M.Value _ _ from Eq.refl _)
                          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i39)))).trans (by
                          let _litex_original := _equal_wd_1_0
                          let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
                          let _wd_1_1 := _value_i39;
                          (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_270380 True.intro))
                          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_10611 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i12 : M.Value) => (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) _raw_i12)))) (Litex.denote _litex_literal.val.argument) = (Litex.absValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i39)))) from rfl))
                        ))).trans _litex_residual)))
                      )
                  )
                have h_263062 : (by
                  let _atomic_wd_1_0 := _object_w358
                  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w358
                          exact (by
                            let _atomic_wd_2_1 := _atomic_wd_1_0
                            exact (by
                              let _litex_abs := _atomic_wd_2_1
                              exact Litex.absNonnegative _litex_abs.val.arg _litex_abs.wd
                            )))
                      )
                  )
                have h_263063 : (by
                  let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                          exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w358 _atomic_wd_1_0 (show @Eq M.Value _ _ from Eq.refl _) (h_263061).symm h_263062))
                      )
                  )
                have h_263064 : (by
                  let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)
                  exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)
                          exact (Litex.inRPos_positive _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (by
                              let _litex_return_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))))
                      )
                  )
                have h_263065 : (by
                  let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)
                  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)
                          exact (Litex.leTrans (Litex.number (M := M) (0 : ℂ)) (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro) _atomic_wd_1_1 h_263063 h_263052))
                      )
                  )
                have h_263066 : (by
                  let _atomic_wd_1_1 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_1 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                          exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w358 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_263061).symm h_263062))
                      )
                  )
                let _object_w359 := (let _wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro);
                let _wd_1_1 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                (Litex.sub _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.positiveRealToComplex (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)))) (by
                  let _atomic_wd_1_0 := _wd_1_1
                  exact (Litex.realToComplex (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro))))))

                have h_263067 : (by
                  let _atomic_wd_1_0 := _object_w359
                  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w359
                          exact (by
                            let _litex_real_result := _atomic_wd_1_0
                            exact Litex.subInR _litex_real_result.val.left _litex_real_result.val.right (by
                            let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                            exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)))) (by
                            let _atomic_wd_2_0 := (_atomic_wd_1_0).val.right
                            exact (by
                              let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
                          ))
                      )
                  )
                let _object_w361 := (let _wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro);
                let _wd_1_1 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                (Litex.add _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.positiveRealToComplex (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)))) (by
                  let _atomic_wd_1_0 := _wd_1_1
                  exact (Litex.realToComplex (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro))))))

                have h_263068 : (by
                  let _atomic_wd_1_0 := _object_w361
                  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w361
                          exact (by
                            let _litex_real_result := _atomic_wd_1_0
                            exact Litex.addInR _litex_real_result.val.left _litex_real_result.val.right (by
                            let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
                            exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)))) (by
                            let _atomic_wd_2_0 := (_atomic_wd_1_0).val.right
                            exact (by
                              let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
                          ))
                      )
                  )
                have h_263069 : (by
                  let _atomic_wd_1_0 := _object_w359
                  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w359
                          exact (Litex.subNonnegative _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                            let _atomic_wd_2_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)
                            exact h_263052)))
                      )
                  )
                have h_263070 : (by
                  let _atomic_wd_1_0 := _object_w361
                  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w361
                          exact (by
                            let _litex_zero_bound := _atomic_wd_1_0
                            exact Litex.addNonnegative _litex_zero_bound.val.left _litex_zero_bound.val.right _litex_zero_bound.wd.1 _litex_zero_bound.wd.2 (by
                            let _atomic_wd_2_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)
                            exact h_263065) (by
                            let _atomic_wd_2_1 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                            exact h_263066)
                          ))
                      )
                  )
                have h_263071 : (by
                  let _atomic_wd_1_1 := _object_w359
                  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_1 := _object_w359
                          exact h_263069)
                      )
                  )
                have h_263072 : (by
                  let _atomic_wd_1_1 := _object_w361
                  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_1 := _object_w361
                          exact h_263070)
                      )
                  )
                let _object_w362 := (let _wd_1_0 := _object_w359;
                let _wd_1_1 := _object_w361;
                (Litex.mul _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (M.real_subset_complex _ h_263067)) (by
                  let _atomic_wd_1_0 := _wd_1_1
                  exact (M.real_subset_complex _ h_263068))))

                have h_263073 : (by
                  let _atomic_wd_1_0 := _object_w362
                  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w362
                          exact (by
                            let _litex_zero_bound := _atomic_wd_1_0
                            exact Litex.mulNonnegative _litex_zero_bound.val.left _litex_zero_bound.val.right _litex_zero_bound.wd.1 _litex_zero_bound.wd.2 (by
                            let _atomic_wd_2_1 := (_atomic_wd_1_0).val.left
                            exact h_263071) (by
                            let _atomic_wd_2_1 := (_atomic_wd_1_0).val.right
                            exact h_263072)
                          ))
                      )
                  )
                have h_263074 : (by
                  let _chain_wd_263074_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro);
                  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _wd_2_0
                    exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                  let _wd_1_1 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _wd_2_0
                    exact (by
                      let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
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
                  let _chain_wd_263074_1 := _object_w362
                  exact ((by
                    let _equal_wd_1_0 := _chain_wd_263074_0
                    let _equal_wd_1_1 := _chain_wd_263074_1
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
                    let _atomic_wd_1_0 := _chain_wd_263074_1
                    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _chain_wd_263074_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro);
                          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                            let _atomic_wd_1_0 := _wd_2_0
                            exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                          let _wd_1_1 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                            let _atomic_wd_1_0 := _wd_2_0
                            exact (by
                              let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
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
                          let _chain_wd_263074_1 := _object_w362
                          exact (And.intro (let _equal_wd_1_0 := _chain_wd_263074_0;
                          let _equal_wd_1_1 := _chain_wd_263074_1;
                          (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro);
                          let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                          Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) ^ (2 : ℕ)) - ((let _litex_numeric_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                          let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                          Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) ^ (2 : ℕ))) (((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro);
                          let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                          Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) - (let _litex_numeric_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                          let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                          Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member)) * ((let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro);
                          let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                          Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (let _litex_numeric_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                          let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                          Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member))) (Litex.NativeBridge.denoteSub (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                            let _atomic_wd_1_0 := ((_equal_wd_1_0).val.left).val.base
                            exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro);
                          let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                          Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denotePowNatReal ((_equal_wd_1_0).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                            let _atomic_wd_1_0 := ((_equal_wd_1_0).val.right).val.base
                            exact (by
                              let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (let _litex_numeric_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                          let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                          Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member))) (Litex.NativeBridge.denoteMul (_object_w362).val.left (_object_w362).val.right (by
                            let _atomic_wd_1_0 := (_object_w362).val.left
                            exact (M.real_subset_complex _ h_263067)) (by
                            let _atomic_wd_1_0 := (_object_w362).val.right
                            exact (M.real_subset_complex _ h_263068)) _ _ (Litex.NativeBridge.denoteSub (_object_w359).val.left (_object_w359).val.right (_object_w359).wd.1 (_object_w359).wd.2 _ _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro);
                          let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                          Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (let _litex_numeric_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                          let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                          Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denoteAdd (_object_w361).val.left (_object_w361).val.right (_object_w361).wd.1 (_object_w361).wd.2 _ _ (let _litex_numeric_call := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro);
                          let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.positiveRealToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.RPos from (Litex.callInOutput _litex_numeric_call)));
                          Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (let _litex_numeric_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                          let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                          Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member))) (by ring!)))) (by
                            let _atomic_wd_1_0 := _chain_wd_263074_1
                            exact h_263073)))
                      )
                  )

                have h_280169 :=
                  (And.left h_263074)

                have h_280170 :=
                  (And.right h_263074)

                have h_280171 :=
                  h_280169

                have h_280172 :=
                  h_280170

                have h_280327 :=
                  (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w362 (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro);
                  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _wd_2_0
                    exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                  let _wd_1_1 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                    let _atomic_wd_1_0 := _wd_2_0
                    exact (by
                      let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                  (Litex.sub _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (by
                      let _arithmetic := _atomic_wd_1_0
                      exact Litex.powObjInC _arithmetic)) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (by
                      let _arithmetic := _atomic_wd_1_0
                      exact Litex.powObjInC _arithmetic)))) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (Eq.symm h_280169) h_280170)
                let _object_w363 := (let _wd_1_0 := (let _wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro);
                let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                  let _atomic_wd_1_0 := _wd_2_0
                  exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
                let _wd_1_1 := (let _wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                  let _atomic_wd_1_0 := _wd_2_0
                  exact (by
                    let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
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

                have h_263075 : (by
                  let _atomic_wd_1_1 := _object_w363
                  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_1 := _object_w363
                          exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _object_w362 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_280169).symm h_263073))
                      )
                  )
                let _object_w364 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro);
                let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (by
                    let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

                let _object_w365 := (let _wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro);
                let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))

                have h_263076 : (by
                  let _atomic_wd_1_0 := _object_w364
                  let _atomic_wd_1_1 := _object_w365
                  exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w364
                          let _atomic_wd_1_1 := _object_w365
                          exact (Litex.subNonnegativeToLe _object_w363 (by
                            let _atomic_wd_2_0 := _atomic_wd_1_1
                            exact (Litex.powStructuralInR _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
                              exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)))))) (by
                            let _atomic_wd_2_0 := _atomic_wd_1_0
                            exact (Litex.powStructuralInR _atomic_wd_2_0 (by
                              let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
                              exact (by
                                let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))))) h_263075))
                      )
                  )
                have h_263077 : (by
                  let _atomic_wd_1_0 := _object_w364
                  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w364
                          exact (Litex.powStructuralInR _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                            exact (by
                              let _litex_return_call := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i39 (h_10610 (M := M)) h_270380 True.intro)
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
                      )
                  )
                have h_263078 : (by
                  let _atomic_wd_1_0 := _object_w365
                  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w365
                          exact (Litex.powStructuralInR _atomic_wd_1_0 (by
                            let _atomic_wd_2_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro)
                            exact (Litex.inRPos_real (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro) (Litex.callInOutput (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i39 (h_20132 (M := M)) h_270380 True.intro))))))
                      )
                  )
                have h_263079 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (4 : ℂ)) :=
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
                let _object_w367 := (let _wd_1_0 := _object_w364;
                let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
                (Litex.div _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (M.real_subset_complex _ h_263077)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

                let _object_w368 := (let _wd_1_0 := _object_w365;
                let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
                (Litex.div _wd_1_0 _wd_1_1 (by
                  let _atomic_wd_1_0 := _wd_1_0
                  exact (M.real_subset_complex _ h_263078)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

                have h_263080 : (by
                  let _atomic_wd_1_0 := _object_w367
                  let _atomic_wd_1_1 := _object_w368
                  exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := _object_w367
                          let _atomic_wd_1_1 := _object_w368
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
                            exact h_263076) (Litex.sameRefl _litex_monotone_left.val.right)
                          ))
                      )
                  )
                have h_302298 : Litex.Le (let _object_w372 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w372 (h_10610 (M := M)) (by
                  let _atomic_wd_1_0 := _object_w372
                  exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) _object_w367 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          have h_302297 : Litex.In _value_i39 (Litex.N (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  h_270380
                                )
                            )
                          have h_302307 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i39 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.naturalNonnegative _value_i39 h_302297)
                                )
                            )
                          exact ((h_156832 (M := M)) _value_i39 h_302297)
                        )
                      )
                  )
                have h_263081 : (by
                  let _atomic_wd_1_0 := (let _object_w372 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w372 (h_10610 (M := M)) (by
                    let _atomic_wd_1_0 := _object_w372
                    exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                  let _atomic_wd_1_1 := _object_w367
                  exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_1_0 := (let _object_w372 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                          (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w372 (h_10610 (M := M)) (by
                            let _atomic_wd_1_0 := _object_w372
                            exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                          let _atomic_wd_1_1 := _object_w367
                          exact h_302298)
                      )
                  )
                have h_303990 : Litex.Same (let _object_w375 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w375 (h_20132 (M := M)) (by
                  let _atomic_wd_1_0 := _object_w375
                  exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) _object_w368 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          have h_303989 : Litex.In _value_i39 (Litex.N (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  h_270380
                                )
                            )
                          have h_303999 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i39 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.naturalNonnegative _value_i39 h_303989)
                                )
                            )
                          exact ((h_198188 (M := M)) _value_i39 h_303989)
                        )
                      )
                  )
                have h_263082 : (by
                  let _equal_wd_1_0 := (let _object_w375 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w375 (h_20132 (M := M)) (by
                    let _atomic_wd_1_0 := _object_w375
                    exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                  let _equal_wd_1_1 := _object_w368
                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                  (by
                    litex_checked_step =>
                      exact (
                        h_303990
                      )
                  )
                have h_263083 : (by
                  let _chain_wd_263083_4 := _object_w368
                  let _chain_wd_263083_5 := (let _object_w375 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w375 (h_20132 (M := M)) (by
                    let _atomic_wd_1_0 := _object_w375
                    exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                  exact ((by
                    let _atomic_wd_1_0 := (let _object_w372 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                    (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w372 (h_10610 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w372
                      exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                    let _atomic_wd_1_1 := _object_w367
                    exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)) ∧ (((by
                    let _atomic_wd_1_0 := _object_w367
                    let _atomic_wd_1_1 := _object_w368
                    exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)) ∧ ((by
                    let _equal_wd_1_0 := _chain_wd_263083_4
                    let _equal_wd_1_1 := _chain_wd_263083_5
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _chain_wd_263083_4 := _object_w368
                          let _chain_wd_263083_5 := (let _object_w375 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                          (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w375 (h_20132 (M := M)) (by
                            let _atomic_wd_1_0 := _object_w375
                            exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                          exact (And.intro (by
                            let _atomic_wd_1_0 := (let _object_w372 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                            (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w372 (h_10610 (M := M)) (by
                              let _atomic_wd_1_0 := _object_w372
                              exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                            let _atomic_wd_1_1 := _object_w367
                            exact h_302298) (And.intro (by
                            let _atomic_wd_1_0 := _object_w367
                            let _atomic_wd_1_1 := _object_w368
                            exact h_263080) (h_303990).symm)))
                      )
                  )

                have h_304367 :=
                  (And.left h_263083)

                have h_304368 :=
                  (And.left (And.right h_263083))

                have h_304369 :=
                  (And.right (And.right h_263083))

                have h_304370 :=
                  h_304367

                have h_304371 :=
                  h_304368

                have h_304372 :=
                  h_304369

                have h_304737 :=
                  (Litex.leTrans (let _object_w372 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w372 (h_10610 (M := M)) (by
                    let _atomic_wd_1_0 := _object_w372
                    exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) _object_w367 _object_w368 h_304367 h_304368)

                have h_304738 :=
                  (Litex.leOfSame (let _object_w372 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w372 (h_10610 (M := M)) (by
                    let _atomic_wd_1_0 := _object_w372
                    exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) (let _object_w372 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w372 (h_10610 (M := M)) (by
                    let _atomic_wd_1_0 := _object_w372
                    exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) _object_w368 (let _object_w375 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w375 (h_20132 (M := M)) (by
                    let _atomic_wd_1_0 := _object_w375
                    exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) (Litex.sameRefl (let _object_w372 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w372 (h_10610 (M := M)) (by
                    let _atomic_wd_1_0 := _object_w372
                    exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))) h_304369 (Litex.leTrans (let _object_w372 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w372 (h_10610 (M := M)) (by
                    let _atomic_wd_1_0 := _object_w372
                    exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) _object_w367 _object_w368 h_304367 h_304368))

                have h_304739 :=
                  (Litex.leOfSame _object_w367 _object_w367 _object_w368 (let _object_w375 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w375 (h_20132 (M := M)) (by
                    let _atomic_wd_1_0 := _object_w375
                    exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro)) (Litex.sameRefl _object_w367) h_304369 h_304368)
                show (fun (_raw_i39 : M.Value) => (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) _raw_i39) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) _raw_i39) = M.number (_s : ℂ) ∧ _r ≤ _s)) (M.addValue _raw_i39 (M.number 1))
                exact (by
                  let _atomic_wd_1_0 := (let _object_w372 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _object_w372 (h_10610 (M := M)) (by
                    let _atomic_wd_1_0 := _object_w372
                    exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                  let _atomic_wd_1_1 := (let _object_w375 := (Litex.add _value_i39 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i39 h_270328) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _object_w375 (h_20132 (M := M)) (by
                    let _atomic_wd_1_0 := _object_w375
                    exact (Litex.addInN _value_i39 (Litex.number (M := M) (1 : ℂ)) h_270380 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) True.intro))
                  exact (Litex.leOfSame _atomic_wd_1_0 _atomic_wd_1_0 _object_w368 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_303990).symm h_304737))
              ) _value_i39 h_263369 h_263370
            )
          )
      )
    exact (by
      let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) _value_i38 (h_10610 (M := M)) h_263354 True.intro)
      let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) _value_i38 (h_20132 (M := M)) h_263354 True.intro)
      exact (by
        have h_308176 : Litex.In _value_i38 (Litex.Z (M := M)) :=
          (Litex.naturalToInteger _value_i38 h_263354)
        have h_308201 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i38 :=
          h_263355
        exact (Litex.leOfSame _atomic_wd_1_0 _atomic_wd_1_0 _atomic_wd_1_1 _atomic_wd_1_1 (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i11 (M := M))) (Litex.sameRefl _value_i38)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i15 (M := M))) (Litex.sameRefl _value_i38)) ((fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value : Litex.Obj (M := M) _Host) => h_304775 (Litex.denote _value)) _value_i38 h_308176 h_308201))
      ))
  )

theorem h_308521 : Litex.Le (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro) (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro) :=
  (by
    have h_308520 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
          )
      )
    have h_308532 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative (Litex.number (M := M) (2 : ℂ)) h_308520)
          )
      )
    exact ((h_263051 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_308520)
  )

theorem h_309115 : (by
  let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
  let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
  exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
    let _atomic_wd_1_1 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
    exact (h_308521 (M := M)))

noncomputable def _object_w384 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (64 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (64 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (64 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (64 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (64 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_309179 : (by
  let _equal_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
  let _equal_wd_1_1 := (_object_w384 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (let _equal_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro);
  let _equal_wd_1_1 := (_object_w384 (M := M));
  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.number (2 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (64 : ℂ))) from by
    have _litex_residual : (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (2 : ℂ))))) = (M.divValue (M.number (1 : ℂ)) (M.number (64 : ℂ))) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (4 : ℂ));
    let _wd_1_1 := (let _wd_2_0 := (_object_w66 (M := M));
    let _wd_2_1 := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (4 : ℕ) (by
      let _atomic_wd_1_0 := (_object_w66 (M := M))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (2 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (2 : ℕ)) (4 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((4 : ℕ) : ℂ)) ((2 : ℂ) ^ (2 : ℕ)) ((4 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((4 : ℕ) : ℂ)) (by norm_num))));
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (4 : ℂ)) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (256 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (_atomic_wd_1_0).val.exponent (4 : ℕ) (by
        let _atomic_wd_2_0 := (_object_w66 (M := M))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
        let _atomic_wd_2_0 := (_atomic_wd_1_0).val.exponent
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((2 : ℂ) ^ (2 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (2 : ℕ)) (4 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber (_atomic_wd_1_0).val.exponent (Litex.number (M := M) ((4 : ℕ) : ℂ)) ((2 : ℂ) ^ (2 : ℕ)) ((4 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((4 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))).trans (congrArg M.number (by norm_num : (((1 : ℂ) / (4 : ℂ)) ^ (4 : ℕ)) = ((1 : ℂ) / (256 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (256 : ℂ)))))));
    let _equal_wd_2_1 := _equal_wd_1_1;
    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 ((4 : ℂ) * (((1 : ℂ) / (4 : ℂ)) ^ (4 : ℕ))) ((1 : ℂ) / (64 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denotePowNatReal ((_equal_wd_2_0).val.right).val.base ((_equal_wd_2_0).val.right).val.exponent (4 : ℕ) (by
      let _atomic_wd_1_0 := (_object_w66 (M := M))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (4 : ℂ)) ((1 : ℝ) / (4 : ℝ)) (by norm_num)))) (by
      let _atomic_wd_1_0 := ((_equal_wd_2_0).val.right).val.exponent
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) ^ (2 : ℕ)) (Litex.N (M := M)) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInNOfEq ((2 : ℂ) ^ (2 : ℕ)) (4 : ℕ) (by norm_num)))) (Litex.NativeBridge.sameOfDenoteNumber ((_equal_wd_2_0).val.right).val.exponent (Litex.number (M := M) ((4 : ℕ) : ℂ)) ((2 : ℂ) ^ (2 : ℕ)) ((4 : ℕ) : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) ((4 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) ((_object_w66 (M := M))).wd.1 ((_object_w66 (M := M))).wd.2.1 ((_object_w66 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (64 : ℂ)) (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2.1 (_equal_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (64 : ℂ))) (by norm_num))))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i15 (M := M))) (M.number (2 : ℂ))))).trans (by
    let _litex_original := _equal_wd_1_0
    let _litex_literal := (let _wd_1_0 := (_object_i15 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_20133 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i16 : M.Value) => (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) _raw_i16)))) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (4 : ℂ)) (M.powValue (M.divValue (M.number (1 : ℂ)) (M.number (4 : ℂ))) (M.powValue (M.number (2 : ℂ)) (M.number (2 : ℂ))))) from rfl))
  ))).trans _litex_residual)))

theorem h_309663 : (by
  let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
  let _atomic_wd_1_1 := (_object_w384 (M := M))
  exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_10610 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro)
    let _atomic_wd_1_1 := (_object_w384 (M := M))
    exact (Litex.leOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.callTarget Litex.StandardSetValue.natural (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i16 : M.Value) => True) (_object_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_20132 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) True.intro) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_309179 (M := M)) (h_308521 (M := M))))
end LitexCompiled.file_lean_x2f_examples_x2f_newton_x5f_residual_x5f_bound_x2f_statement_x2e_lit
