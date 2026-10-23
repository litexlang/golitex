import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_closed_x5f_unit_x5f_interval_x2f_statement_x2e_lit

universe u v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_i1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i2 (Litex.R (M := M))) => ((Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2) ∧ (Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ))))))
theorem h_130 : Litex.IsSet (_object_i1 (M := M)) :=
  (by
    let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_67 : Litex.In _value_i2 (Litex.R (M := M))) => ((Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2) ∧ (Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ))))))
    exact (Litex.isSet _atomic_wd_1_0))
theorem h_131 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (Litex.sameRefl (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i2 (Litex.R (M := M))) => ((Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2) ∧ (Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ)))))))

noncomputable def _object_w4 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_132 : (by
  let _atomic_wd_1_0 := (_object_w4 (M := M))
  exact Litex.In _atomic_wd_1_0 (_object_i1 (M := M))) :=
  (by
    let _atomic_wd_1_0 := (_object_w4 (M := M))
    exact (Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl _atomic_wd_1_0) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_131 (M := M)))).symm (by
      let _atomic_wd_2_0 := _atomic_wd_1_0
      let _atomic_wd_2_1 := (_object_i1 (M := M))
      exact (by
        let _set := _atomic_wd_2_1
        exact (Litex.inSetBuilder_iff _atomic_wd_2_0 _set.val.bound _set.val.predicate).mpr ⟨(by
        let _atomic_wd_3_0 := _atomic_wd_2_0
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2.1 (_atomic_wd_3_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))), (And.intro (by
        let _atomic_wd_3_1 := _atomic_wd_2_0
        exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_3_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
          let _atomic_wd_4_0 := _atomic_wd_3_1
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_4_0).wd.1 (_atomic_wd_4_0).wd.2.1 (_atomic_wd_4_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num))))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_3_1 (by
          let _atomic_wd_4_0 := _atomic_wd_3_1
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_4_0).wd.1 (_atomic_wd_4_0).wd.2.1 (_atomic_wd_4_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (2 : ℝ)) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_3_1 (by
          let _atomic_wd_4_0 := _atomic_wd_3_1
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_4_0).wd.1 (_atomic_wd_4_0).wd.2.1 (_atomic_wd_4_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (by
        let _atomic_wd_3_0 := _atomic_wd_2_0
        exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_3_0 (Litex.number (M := M) (1 : ℂ)) (by
          let _atomic_wd_4_0 := _atomic_wd_3_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_4_0).wd.1 (_atomic_wd_4_0).wd.2.1 (_atomic_wd_4_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_3_0 (by
          let _atomic_wd_4_0 := _atomic_wd_3_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_4_0).wd.1 (_atomic_wd_4_0).wd.2.1 (_atomic_wd_4_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) = ((1 : ℝ) / (2 : ℝ)) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_3_0 (by
          let _atomic_wd_4_0 := _atomic_wd_3_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_4_0).wd.1 (_atomic_wd_4_0).wd.2.1 (_atomic_wd_4_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))⟩))))

theorem h_163 : (M.mem (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) (M.standard Litex.StandardSetValue.real)) :=
  (((Litex.inSetBuilder_iff (_object_w4 (M := M)) ((_object_i1 (M := M))).val.bound ((_object_i1 (M := M))).val.predicate).mp (Litex.inOfSame (_object_w4 (M := M)) (_object_w4 (M := M)) (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (_object_w4 (M := M))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_131 (M := M))) (h_132 (M := M))))).choose

theorem h_164 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number (_s : ℂ) ∧ _r ≤ _s)) ∧ ((∃ (_r _s : ℝ), (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s))) :=
  (((Litex.inSetBuilder_iff (_object_w4 (M := M)) ((_object_i1 (M := M))).val.bound ((_object_i1 (M := M))).val.predicate).mp (Litex.inOfSame (_object_w4 (M := M)) (_object_w4 (M := M)) (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (_object_w4 (M := M))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_131 (M := M))) (h_132 (M := M))))).choose_spec

theorem h_165 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (_object_w4 (M := M)) :=
  (And.left (((Litex.inSetBuilder_iff (_object_w4 (M := M)) ((_object_i1 (M := M))).val.bound ((_object_i1 (M := M))).val.predicate).mp (Litex.inOfSame (_object_w4 (M := M)) (_object_w4 (M := M)) (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (_object_w4 (M := M))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_131 (M := M))) (h_132 (M := M))))).choose_spec)

theorem h_166 : Litex.Le (_object_w4 (M := M)) (Litex.number (M := M) (1 : ℂ)) :=
  (And.right (((Litex.inSetBuilder_iff (_object_w4 (M := M)) ((_object_i1 (M := M))).val.bound ((_object_i1 (M := M))).val.predicate).mp (Litex.inOfSame (_object_w4 (M := M)) (_object_w4 (M := M)) (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (_object_w4 (M := M))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_131 (M := M))) (h_132 (M := M))))).choose_spec)

theorem h_168 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_183 : Litex.In _value_i3 (_object_i1 (M := M))), (Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3) ∧ (Litex.Le _value_i3 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 h_183
    have h_184 : (M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) :=
      (by
        litex_checked_step =>
          exact (
            (((Litex.inSetBuilder_iff _value_i3 ((_object_i1 (M := M))).val.bound ((_object_i1 (M := M))).val.predicate).mp (Litex.inOfSame _value_i3 _value_i3 (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl _value_i3) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_131 (M := M))) h_183))).choose
          )
      )
    have h_185 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i3) = M.number (_s : ℂ) ∧ _r ≤ _s)) ∧ ((∃ (_r _s : ℝ), (Litex.denote _value_i3) = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s))) :=
      (by
        litex_checked_step =>
          exact (
            (((Litex.inSetBuilder_iff _value_i3 ((_object_i1 (M := M))).val.bound ((_object_i1 (M := M))).val.predicate).mp (Litex.inOfSame _value_i3 _value_i3 (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl _value_i3) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_131 (M := M))) h_183))).choose_spec
          )
      )
    have h_186 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
      (by
        litex_checked_step =>
          exact (
            (And.left (((Litex.inSetBuilder_iff _value_i3 ((_object_i1 (M := M))).val.bound ((_object_i1 (M := M))).val.predicate).mp (Litex.inOfSame _value_i3 _value_i3 (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl _value_i3) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_131 (M := M))) h_183))).choose_spec)
          )
      )
    have h_187 : Litex.Le _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (And.right (((Litex.inSetBuilder_iff _value_i3 ((_object_i1 (M := M))).val.bound ((_object_i1 (M := M))).val.predicate).mp (Litex.inOfSame _value_i3 _value_i3 (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl _value_i3) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_131 (M := M))) h_183))).choose_spec)
          )
      )
    have h_167 : (Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3) ∧ (Litex.Le _value_i3 (Litex.number (M := M) (1 : ℂ))) :=
      (by
        litex_checked_step =>
          exact (
            (And.intro h_186 h_187)
          )
      )
    have h_200 :=
      (And.left h_167)
    have h_201 :=
      (And.right h_167)
    have h_202 :=
      h_200
    have h_203 :=
      h_201
    have h_277 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.N (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.weakIntegerLowerBoundInN _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) h_186 h_203)
          )
      )
    have h_292 :=
      (Litex.leTrans (Litex.number (M := M) (0 : ℂ)) _value_i3 (Litex.number (M := M) (1 : ℂ)) h_200 h_201)
    exact h_167
  )

theorem h_293 : Litex.Subset (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (Litex.subsetOfForall (_object_i1 (M := M)) (Litex.R (M := M)) (by
    intro _Host_i4 _rep_i4 _value_i4 h_311
    have h_312 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
      (by
        litex_checked_step =>
          exact (
            (((Litex.inSetBuilder_iff _value_i4 ((_object_i1 (M := M))).val.bound ((_object_i1 (M := M))).val.predicate).mp (Litex.inOfSame _value_i4 _value_i4 (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl _value_i4) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_131 (M := M))) h_311))).choose
          )
      )
    have h_313 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i4) = M.number (_s : ℂ) ∧ _r ≤ _s)) ∧ ((∃ (_r _s : ℝ), (Litex.denote _value_i4) = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s))) :=
      (by
        litex_checked_step =>
          exact (
            (((Litex.inSetBuilder_iff _value_i4 ((_object_i1 (M := M))).val.bound ((_object_i1 (M := M))).val.predicate).mp (Litex.inOfSame _value_i4 _value_i4 (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl _value_i4) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_131 (M := M))) h_311))).choose_spec
          )
      )
    have h_314 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
      (by
        litex_checked_step =>
          exact (
            (And.left (((Litex.inSetBuilder_iff _value_i4 ((_object_i1 (M := M))).val.bound ((_object_i1 (M := M))).val.predicate).mp (Litex.inOfSame _value_i4 _value_i4 (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl _value_i4) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_131 (M := M))) h_311))).choose_spec)
          )
      )
    have h_315 : Litex.Le _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (And.right (((Litex.inSetBuilder_iff _value_i4 ((_object_i1 (M := M))).val.bound ((_object_i1 (M := M))).val.predicate).mp (Litex.inOfSame _value_i4 _value_i4 (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl _value_i4) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_131 (M := M))) h_311))).choose_spec)
          )
      )
    have h_295 : Litex.In _value_i4 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_312
          )
      )
    exact h_295
  ))
end LitexCompiled.file_lean_x2f_examples_x2f_closed_x5f_unit_x5f_interval_x2f_statement_x2e_lit
