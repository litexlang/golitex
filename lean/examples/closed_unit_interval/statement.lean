import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_closed_x5f_unit_x5f_interval_x2f_statement_x2e_lit

universe u v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_i1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i2 (Litex.R (M := M))) => ((Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2) ∧ (Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ))))))
theorem h_146 : Litex.IsSet (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_75 : Litex.In _value_i2 (Litex.R (M := M))) => ((Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2) ∧ (Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ))))))
          exact (Litex.isSet _atomic_wd_1_0))
      )
  )
theorem h_147 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i2 (Litex.R (M := M))) => ((Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2) ∧ (Litex.Le _value_i2 (Litex.number (M := M) (1 : ℂ)))))))
      )
  )

noncomputable def _object_w10 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_148 : (by
  let _atomic_wd_1_0 := (_object_w10 (M := M))
  exact Litex.In _atomic_wd_1_0 (_object_i1 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w10 (M := M))
          exact (Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl _atomic_wd_1_0) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_147 (M := M)))).symm (by
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
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_4_0).wd.1 (_atomic_wd_4_0).wd.2.1 (_atomic_wd_4_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_1).wd.1 (_atomic_wd_3_1).wd.2.1 (_atomic_wd_3_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
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
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_4_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_4_0).wd.1 (_atomic_wd_4_0).wd.2.1 (_atomic_wd_4_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2.1 (_atomic_wd_3_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))⟩))))
      )
  )

theorem h_179 : (M.mem (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) (M.standard Litex.StandardSetValue.real)) :=
  (by
    litex_complete =>
      exact (
        ((let _litex_builder := (_object_i1 (M := M)); (Litex.inSetBuilderObj_iff (_object_w10 (M := M)) _litex_builder).mp (Litex.inOfSame (_object_w10 (M := M)) (_object_w10 (M := M)) (_object_i1 (M := M)) _litex_builder (Litex.sameRefl (_object_w10 (M := M))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_147 (M := M))) (h_148 (M := M))))).choose
      )
  )

theorem h_180 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number (_s : ℂ) ∧ _r ≤ _s)) ∧ ((∃ (_r _s : ℝ), (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s))) :=
  (by
    litex_complete =>
      exact (
        ((let _litex_builder := (_object_i1 (M := M)); (Litex.inSetBuilderObj_iff (_object_w10 (M := M)) _litex_builder).mp (Litex.inOfSame (_object_w10 (M := M)) (_object_w10 (M := M)) (_object_i1 (M := M)) _litex_builder (Litex.sameRefl (_object_w10 (M := M))) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_147 (M := M))) (h_148 (M := M))))).choose_spec
      )
  )

theorem h_181 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (_object_w10 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (And.left (h_180 (M := M)))
      )
  )

theorem h_182 : Litex.Le (_object_w10 (M := M)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (And.right (h_180 (M := M)))
      )
  )

theorem h_184 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_199 : Litex.In _value_i3 (_object_i1 (M := M))), (Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3) ∧ (Litex.Le _value_i3 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_199
          have h_200 : (M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) :=
            (by
              litex_checked_step =>
                exact (
                  ((let _litex_builder := (_object_i1 (M := M)); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp (Litex.inOfSame _value_i3 _value_i3 (_object_i1 (M := M)) _litex_builder (Litex.sameRefl _value_i3) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_147 (M := M))) h_199))).choose
                )
            )
          have h_201 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i3) = M.number (_s : ℂ) ∧ _r ≤ _s)) ∧ ((∃ (_r _s : ℝ), (Litex.denote _value_i3) = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s))) :=
            (by
              litex_checked_step =>
                exact (
                  ((let _litex_builder := (_object_i1 (M := M)); (Litex.inSetBuilderObj_iff _value_i3 _litex_builder).mp (Litex.inOfSame _value_i3 _value_i3 (_object_i1 (M := M)) _litex_builder (Litex.sameRefl _value_i3) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_147 (M := M))) h_199))).choose_spec
                )
            )
          have h_202 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (And.left h_201)
                )
            )
          have h_203 : Litex.Le _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (And.right h_201)
                )
            )
          have h_183 : (Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3) ∧ (Litex.Le _value_i3 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (And.intro h_202 h_203)
                )
            )
          have h_216 :=
            (And.left h_183)
          have h_217 :=
            (And.right h_183)
          have h_218 :=
            h_216
          have h_219 :=
            h_217
          have h_312 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.weakIntegerLowerBoundInN _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) h_202 h_219)
                )
            )
          have h_327 :=
            (Litex.leTrans (Litex.number (M := M) (0 : ℂ)) _value_i3 (Litex.number (M := M) (1 : ℂ)) h_216 h_217)
          exact h_183
        )
      )
  )

theorem h_328 : Litex.Subset (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.subsetOfForall (_object_i1 (M := M)) (Litex.R (M := M)) (by
          intro _Host_i4 _rep_i4 _value_i4 h_347
          have h_348 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
            (by
              litex_checked_step =>
                exact (
                  ((let _litex_builder := (_object_i1 (M := M)); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp (Litex.inOfSame _value_i4 _value_i4 (_object_i1 (M := M)) _litex_builder (Litex.sameRefl _value_i4) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_147 (M := M))) h_347))).choose
                )
            )
          have h_349 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i4) = M.number (_s : ℂ) ∧ _r ≤ _s)) ∧ ((∃ (_r _s : ℝ), (Litex.denote _value_i4) = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s))) :=
            (by
              litex_checked_step =>
                exact (
                  ((let _litex_builder := (_object_i1 (M := M)); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp (Litex.inOfSame _value_i4 _value_i4 (_object_i1 (M := M)) _litex_builder (Litex.sameRefl _value_i4) (((Litex.sameRefl (_object_i1 (M := M)))).trans (h_147 (M := M))) h_347))).choose_spec
                )
            )
          have h_350 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (And.left h_349)
                )
            )
          have h_351 : Litex.Le _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (And.right h_349)
                )
            )
          have h_331 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_348
                )
            )
          exact h_331
        ))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_closed_x5f_unit_x5f_interval_x2f_statement_x2e_lit
