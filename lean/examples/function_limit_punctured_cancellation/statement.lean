import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_punctured_x5f_cancellation_x2f_statement_x2e_lit

universe u v4 v9 v18
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.powValue _raw_i2 (M.number (2 : ℂ))) _raw_i2)) (by
  intro _raw_i2 h_43 h_1
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_43)
  have h_43 : Litex.In _value_i2 (Litex.R (M := M)) := h_43
  have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i2 = (M.number (0 : ℂ))))
            exact h_1)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_43 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    let _wd_1_1 := _value_i2;
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (M.real_subset_complex _ h_43)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (M.real_subset_complex _ h_43) h_1))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_43 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    let _wd_1_1 := _value_i2;
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_power := _atomic_wd_2_0
        have _elaborated_power_base := (M.real_subset_complex _ h_43)
        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
        exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
      )) (M.real_subset_complex _ h_43) h_1))
    exact (Litex.divInR (_atomic_wd_1_0).val.left _value_i2 (by
      let _litex_power := (_atomic_wd_1_0).val.left
      have _elaborated_power_base := h_43
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInR _litex_power _recorded_power_base
    ) h_43 (_atomic_wd_1_0).wd.2.2))))
theorem h_150 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_151 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_157 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_167 : Litex.In _value_i4 (Litex.RPos (M := M))), ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_173 : Litex.In _value_i5 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_171 : Litex.In _value_i6 (Litex.R (M := M))) => ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))))), (by
  have h_174 : (M.mem (Litex.denote _value_i5) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_171 : Litex.In _value_i6 (Litex.R (M := M))) => ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i5 _litex_builder).mp h_173)).choose
        )
    )
  exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i5 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_174) (Litex.numberInC (M := M) (0 : ℂ)));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i5 (Litex.number (M := M) (0 : ℂ)) h_174 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i5 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_174) (Litex.numberInC (M := M) (0 : ℂ)));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i5 (Litex.number (M := M) (0 : ℂ)) h_174 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i4))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_167
          have h_168 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i4 h_167)
                )
            )
          have h_169 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i4 h_168)
                )
            )
          have h_170 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i4 h_168) _litex_zero.symm)
                )
            )
          have h_1006 : Litex.In _value_i4 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_167
                )
            )
          have h_1007 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i4 h_1006)
                )
            )
          have h_1008 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i4 h_1007)
                )
            )
          have h_1009 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i4 h_1007) _litex_zero.symm)
                )
            )
          have h_158 : ((by
            let _atomic_wd_1_1 := (Litex.div _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i4 h_1006) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)) ∧ ((by
            let _atomic_wd_1_0 := (Litex.div _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i4 h_1006) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact Litex.Lt _atomic_wd_1_0 _value_i4)) :=
            (by
              litex_checked_step =>
                exact (
                  (And.intro (by
                    let _atomic_wd_1_1 := (Litex.div _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i4 h_1006) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
                    exact (by
                      let _litex_positive_result := _atomic_wd_1_1
                      exact Litex.divPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2.1 _litex_positive_result.wd.2.2 h_1007 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))
                    )) (by
                    let _atomic_wd_1_0 := (Litex.div _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i4 h_1006) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
                    exact (Litex.divByGtOneLessSelf _atomic_wd_1_0 h_1007 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
                )
            )

          have h_2137 :=
            (And.left h_158)

          have h_2138 :=
            (And.right h_158)

          have h_2139 :=
            h_2137

          have h_2140 :=
            h_2138

          have h_2233 :=
            (Litex.ltTrans (Litex.number (M := M) (0 : ℂ)) (Litex.div _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i4 h_1006) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) _value_i4 h_2137 h_2138)
          let _object_w15 := (Litex.div _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i4 h_1006) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

          have h_159 : (by
            let _atomic_wd_1_0 := _object_w15
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w15
                    exact (fun _litex_equal => (Litex.ltNotSame (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0 h_2137) _litex_equal.symm))
                )
            )
          let _object_w16 := (let _wd_1_0 := _object_w15;
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w15
            exact (Litex.divInC _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i4 h_1006) (Litex.numberInC (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.2.2)) (Litex.numberInC (M := M) (0 : ℂ))))

          have h_160 : (by
            let _equal_wd_1_0 := _object_w16
            let _equal_wd_1_1 := _object_w15
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w16;
                  let _equal_wd_1_1 := _object_w15;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i4 (Litex.positiveRealToComplex _value_i4 h_1006)) / (2 : ℂ)) - (0 : ℂ)) ((Litex.NativeBridge.asComplex _value_i4 (Litex.positiveRealToComplex _value_i4 h_1006)) / (2 : ℂ)) (Litex.NativeBridge.denoteSub (_equal_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv _value_i4 (Litex.number (M := M) (2 : ℂ)) (_object_w15).wd.1 (_object_w15).wd.2.1 (_object_w15).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.positiveRealToComplex _value_i4 h_1006)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denoteDiv _value_i4 (Litex.number (M := M) (2 : ℂ)) (_object_w15).wd.1 (_object_w15).wd.2.1 (_object_w15).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.positiveRealToComplex _value_i4 h_1006)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by
                    have _litex_nz_0 : ((2 : ℂ) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))
                )
            )
          have h_161 : (by
            let _chain_wd_161_0 := (let _wd_1_0 := _object_w16;
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _object_w16
              exact (Litex.subInR (_object_w16).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.divInR _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.inRPos_real _value_i4 h_1006) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) ((_object_w16).val.left).wd.2.2) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
            let _chain_wd_161_1 := (let _wd_1_0 := _object_w15;
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _object_w15
              exact (Litex.divInR _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.inRPos_real _value_i4 h_1006) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))))
            let _chain_wd_161_2 := _chain_wd_161_1
            let _chain_wd_161_3 := _object_w15
            exact ((by
              let _equal_wd_1_0 := _chain_wd_161_0
              let _equal_wd_1_1 := _chain_wd_161_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_161_2
              let _equal_wd_1_1 := _chain_wd_161_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_161_0 := (let _wd_1_0 := _object_w16;
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _object_w16
                      exact (Litex.subInR (_object_w16).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.divInR _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.inRPos_real _value_i4 h_1006) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) ((_object_w16).val.left).wd.2.2) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                    let _chain_wd_161_1 := (let _wd_1_0 := _object_w15;
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _object_w15
                      exact (Litex.divInR _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.inRPos_real _value_i4 h_1006) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))))
                    let _chain_wd_161_2 := _chain_wd_161_1
                    let _chain_wd_161_3 := _object_w15
                    exact (And.intro (congrArg (Litex.absValue (M := M)) (show (M.subValue (M.divValue (Litex.denote _value_i4) (M.number (2 : ℂ))) (M.number (0 : ℂ))) = (M.divValue (Litex.denote _value_i4) (M.number (2 : ℂ))) from h_160)) (let _equal_wd_1_0 := _chain_wd_161_2;
                    let _equal_wd_1_1 := _chain_wd_161_3;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                      let _litex_abs := _equal_wd_1_0
                      exact (Litex.absOfNonnegative _litex_abs.val.arg _litex_abs.wd (Litex.ltToLe (Litex.number (M := M) 0) _equal_wd_1_1 (by
                      let _atomic_wd_1_1 := _object_w15
                      exact h_2137)))
                    )))))
                )
            )

          have h_2811 :=
            (And.left h_161)

          have h_2812 :=
            (And.right h_161)

          have h_2813 :=
            h_2811

          have h_2814 :=
            h_2812

          have h_2815 :=
            (Eq.trans h_2811 h_2812)
          have h_166 : ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_2819 : Litex.In _value_i7 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_2816 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ))))), (by
            have h_2820 : (M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_2816 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i7 _litex_builder).mp h_2819)).choose
                  )
              )
            exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i7 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_2820) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i7 (Litex.number (M := M) (0 : ℂ)) h_2820 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i7 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_2820) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i7 (Litex.number (M := M) (0 : ℂ)) h_2820 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i4))
          ) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i7 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _object_w15) (Litex.isSet _object_w15)
                    have h_3707 : Litex.In _value_i7 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_3704 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)))) := (by
                      let _atomic_wd_1_0 := _object_w15
                      let _atomic_wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_3662 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ))))
                      exact (by
                        let _set := _atomic_wd_1_1
                        exact (Litex.inSetBuilder_iff _atomic_wd_1_0 _set.val.bound _set.val.predicate).mpr ⟨(by
                        let _atomic_wd_2_0 := _object_w15
                        exact (Litex.divInR _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.inRPos_real _value_i4 h_1006) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (_atomic_wd_2_0).wd.2.2)), (by
                        let _atomic_wd_2_0 := _object_w15
                        exact h_159)⟩))
                    have h_3708 : (M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_3704 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i7 _litex_builder).mp h_3707)).choose
                          )
                      )
                    have h_3709 : (¬ ((Litex.denote _value_i7) = (M.number (0 : ℂ)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_3704 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i7 _litex_builder).mp h_3707)).choose_spec
                          )
                      )
                    have h_3710 : Litex.Same _value_i7 (_object_w16).val.left := rfl
                    have h_3713 : ((by
                      let _atomic_wd_1_1 := (let _wd_1_0 := _object_w16;
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _object_w16
                        exact (Litex.subInR (_object_w16).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.divInR _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.inRPos_real _value_i4 h_1006) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) ((_object_w16).val.left).wd.2.2) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                      exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)) ∧ ((by
                      let _atomic_wd_1_0 := (let _wd_1_0 := _object_w16;
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _object_w16
                        exact (Litex.subInR (_object_w16).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.divInR _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.inRPos_real _value_i4 h_1006) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) ((_object_w16).val.left).wd.2.2) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                      exact Litex.Lt _atomic_wd_1_0 _value_i4)) := (And.intro (by
                      let _atomic_wd_1_1 := (let _wd_1_0 := _object_w16;
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _object_w16
                        exact (Litex.subInR (_object_w16).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.divInR _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.inRPos_real _value_i4 h_1006) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) ((_object_w16).val.left).wd.2.2) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                      exact (Litex.ltOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_object_w16).val.left _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_2815).symm h_2137)) (by
                      let _atomic_wd_1_0 := (let _wd_1_0 := _object_w16;
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _object_w16
                        exact (Litex.subInR (_object_w16).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.divInR _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.inRPos_real _value_i4 h_1006) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) ((_object_w16).val.left).wd.2.2) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                      exact (Litex.ltOfSame (_object_w16).val.left _atomic_wd_1_0 _value_i4 _value_i4 (h_2815).symm (show @Eq M.Value _ _ from Eq.refl _) h_2138)))
                    exact ⟨_value_i7, h_3707, h_3713⟩
                )
            )
          exact h_166
        )
      )
  )

theorem h_5420 : ∀ {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_5448 : Litex.In _value_i9 (Litex.RPos (M := M))), ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_5452 : Litex.In _value_i10 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_5456 : Litex.In _value_i12 (Litex.R (M := M))) => ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_5459 : Litex.In _value_i11 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_5456 : Litex.In _value_i12 (Litex.R (M := M))) => ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ))))) => (by
  have h_5460 : (M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_5456 : Litex.In _value_i12 (Litex.R (M := M))) => ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i11 _litex_builder).mp h_5459)).choose
        )
    )
  exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i11 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_5460) (Litex.numberInC (M := M) (0 : ℂ)));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i11 (Litex.number (M := M) (0 : ℂ)) h_5460 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i11 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_5460) (Litex.numberInC (M := M) (0 : ℂ)));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i11 (Litex.number (M := M) (0 : ℂ)) h_5460 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i10))
))) (let _wd_1_0 := (_object_i1 (M := M));
let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_6413 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i13 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_6413) (Litex.numberInC (M := M) (0 : ℂ)));
(Litex.abs _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.subInR _value_i13 (Litex.number (M := M) (0 : ℂ)) h_6413 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
(by
  have _preimage_target : (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_6669 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i13 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_6669) (Litex.numberInC (M := M) (0 : ℂ)));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i13 (Litex.number (M := M) (0 : ℂ)) h_6669 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
  exact Litex.IsSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_6669 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i13 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_6669) (Litex.numberInC (M := M) (0 : ℂ)));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i13 (Litex.number (M := M) (0 : ℂ)) h_6669 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
  exact (Litex.isSet _atomic_wd_1_0))
  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i26 : Litex.Obj (M := M) M.Value) (h_6926 : Litex.In _value_i26 (Litex.R (M := M))) => ∃ (h_6924 : ¬ Litex.Same _value_i26 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i26 (h_150 (M := M)) h_6926 h_6924) _wd_1_1))
  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_5448
          have h_5449 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i9 h_5448)
                )
            )
          have h_5450 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_5449)
                )
            )
          have h_5451 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_5449) _litex_zero.symm)
                )
            )
          have h_7245 : Litex.In _value_i9 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5448
                )
            )
          have h_7246 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i9 h_7245)
                )
            )
          have h_7247 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_7246)
                )
            )
          have h_7248 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_7246) _litex_zero.symm)
                )
            )
          have h_5427 : ∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (h_7249 : Litex.In _value_i14 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_7253 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_7256 : Litex.In _value_i15 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_7253 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ))))) => (by
            have h_7257 : (M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_7253 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i15 _litex_builder).mp h_7256)).choose
                  )
              )
            exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i15 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_7257) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i15 (Litex.number (M := M) (0 : ℂ)) h_7257 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i15 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_7257) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i15 (Litex.number (M := M) (0 : ℂ)) h_7257 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i14))
          ))) (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_8210 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_8210) (Litex.numberInC (M := M) (0 : ℂ)));
          (Litex.abs _wd_2_0 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_8210 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
          (by
            have _preimage_target : (by
            let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_8466 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_8466) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_8466 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
            exact Litex.IsSet _atomic_wd_1_0) := (by
            let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_8466 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_8466) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_8466 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
            exact (Litex.isSet _atomic_wd_1_0))
            let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i27 : Litex.Obj (M := M) M.Value) (h_8723 : Litex.In _value_i27 (Litex.R (M := M))) => ∃ (h_8721 : ¬ Litex.Same _value_i27 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i27 (h_150 (M := M)) h_8723 h_8721) _wd_1_1))
            exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i14 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)
                    have h_9047 : Litex.In _value_i14 (Litex.RPos (M := M)) := h_7245
                    have h_9048 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i14 h_9047)
                          )
                      )
                    have h_9049 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_9048)
                          )
                      )
                    have h_9050 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_9048) _litex_zero.symm)
                          )
                      )
                    have h_9051 : Litex.Same _value_i14 _value_i9 := rfl
                    have h_5434 : ∀ {_Host_i18 : Type _} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_10016 : Litex.In _value_i18 (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_9055 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                      have h_9056 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9055)).choose
                            )
                        )
                      exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9056) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9056 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9056) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9056 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                    )))), Litex.In _value_i18 (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_10021 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_10021) (Litex.numberInC (M := M) (0 : ℂ)));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_10021 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
                    (by
                      have _preimage_target : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_10374 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_10374) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_10374 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                      exact Litex.IsSet _atomic_wd_1_0) := (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_10374 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_10374) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_10374 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                      exact (Litex.isSet _atomic_wd_1_0))
                      let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i28 : Litex.Obj (M := M) M.Value) (h_10728 : Litex.In _value_i28 (Litex.R (M := M))) => ∃ (h_10726 : ¬ Litex.Same _value_i28 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i28 (h_150 (M := M)) h_10728 h_10726) _wd_1_1))
                      exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i18 _rep_i18 _value_i18 h_10016
                              have h_10017 : (M.mem (Litex.denote _value_i18) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i20 : M.Value) => ∃ (_ : M.mem _raw_i20 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i20 = (M.number (0 : ℂ))))))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_9055 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                        have h_9056 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                          (by
                                            litex_checked_step =>
                                              exact (
                                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9055)).choose
                                              )
                                          )
                                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9056) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9056 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9056) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9056 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                      ))); (Litex.inSetBuilderObj_iff _value_i18 _litex_builder).mp h_10016)).choose
                                    )
                                )
                              have h_10020 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i18) (M.number (0 : ℂ)))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i18) (M.number (0 : ℂ)))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r < _s))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_9055 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                        have h_9056 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                          (by
                                            litex_checked_step =>
                                              exact (
                                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9055)).choose
                                              )
                                          )
                                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9056) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9056 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9056) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9056 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                      ))); (Litex.inSetBuilderObj_iff _value_i18 _litex_builder).mp h_10016)).choose_spec
                                    )
                                )
                              have h_10018 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_9055 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_9056 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9055)).choose
                                      )
                                  )
                                have h_9057 : (¬ ((Litex.denote _value_i19) = (M.number (0 : ℂ)))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9055)).choose_spec
                                      )
                                  )
                                exact (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9056) (Litex.numberInC (M := M) (0 : ℂ)));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9056 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                              )) (Litex.semanticObject (Litex.denote _value_i18) (Litex.isSet _value_i18)) h_10017) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.left h_10020)
                                    )
                                )
                              have h_10019 : Litex.Lt ((fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_9055 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_9056 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9055)).choose
                                      )
                                  )
                                have h_9057 : (¬ ((Litex.denote _value_i19) = (M.number (0 : ℂ)))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9052 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9055)).choose_spec
                                      )
                                  )
                                exact (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9056) (Litex.numberInC (M := M) (0 : ℂ)));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9056 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                              )) (Litex.semanticObject (Litex.denote _value_i18) (Litex.isSet _value_i18)) h_10017) _value_i9 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.right h_10020)
                                    )
                                )
                              have h_12116 : Litex.In _value_i18 (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_11155 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_11156 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11155)).choose
                                      )
                                  )
                                exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11156) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11156 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11156) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11156 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                              ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_10016
                                    )
                                )
                              have h_12117 : (M.mem (Litex.denote _value_i18) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i20 : M.Value) => ∃ (_ : M.mem _raw_i20 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i20 = (M.number (0 : ℂ))))))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_11155 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                        have h_11156 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                          (by
                                            litex_checked_step =>
                                              exact (
                                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11155)).choose
                                              )
                                          )
                                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11156) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11156 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11156) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11156 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                      ))); (Litex.inSetBuilderObj_iff _value_i18 _litex_builder).mp h_12116)).choose
                                    )
                                )
                              have h_12120 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i18) (M.number (0 : ℂ)))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i18) (M.number (0 : ℂ)))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r < _s))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_11155 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                        have h_11156 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                          (by
                                            litex_checked_step =>
                                              exact (
                                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11155)).choose
                                              )
                                          )
                                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11156) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11156 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11156) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11156 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                      ))); (Litex.inSetBuilderObj_iff _value_i18 _litex_builder).mp h_12116)).choose_spec
                                    )
                                )
                              have h_12118 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_11155 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_11156 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11155)).choose
                                      )
                                  )
                                have h_11157 : (¬ ((Litex.denote _value_i19) = (M.number (0 : ℂ)))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11155)).choose_spec
                                      )
                                  )
                                exact (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11156) (Litex.numberInC (M := M) (0 : ℂ)));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11156 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                              )) (Litex.semanticObject (Litex.denote _value_i18) (Litex.isSet _value_i18)) h_12117) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.left h_12120)
                                    )
                                )
                              have h_12119 : Litex.Lt ((fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_11155 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_11156 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11155)).choose
                                      )
                                  )
                                have h_11157 : (¬ ((Litex.denote _value_i19) = (M.number (0 : ℂ)))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11152 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11155)).choose_spec
                                      )
                                  )
                                exact (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11156) (Litex.numberInC (M := M) (0 : ℂ)));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11156 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                              )) (Litex.semanticObject (Litex.denote _value_i18) (Litex.isSet _value_i18)) h_12117) _value_i9 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.right h_12120)
                                    )
                                )
                              let _object_w85 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i22 : Litex.Obj (M := M) M.Value) (h_12121 : Litex.In _value_i22 (Litex.R (M := M))) => ¬ Litex.Same _value_i22 (Litex.number (M := M) (0 : ℂ))))

                              have h_5436 : (by
                                let _atomic_wd_1_1 := _object_w85
                                exact Litex.In _value_i18 _atomic_wd_1_1) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_1 := _object_w85
                                        exact (Litex.inOfSame _value_i18 _value_i18 _atomic_wd_1_1 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                          let _left := _atomic_wd_1_1
                                          let _right := _atomic_wd_1_1
                                          exact (show Litex.Same _left _right from rfl)) h_12117))
                                    )
                                )

                              have h_12132 : (M.mem (Litex.denote _value_i18) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := _object_w85; (Litex.inSetBuilderObj_iff _value_i18 _litex_builder).mp h_5436)).choose
                                    )
                                )

                              have h_12133 : (¬ ((Litex.denote _value_i18) = (M.number (0 : ℂ)))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := _object_w85; (Litex.inSetBuilderObj_iff _value_i18 _litex_builder).mp h_5436)).choose_spec
                                    )
                                )
                              have h_5437 : Litex.In _value_i18 (Litex.R (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_12132
                                    )
                                )
                              have h_5438 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_12133
                                    )
                                )
                              have h_5439 : (by
                                let _chain_wd_5439_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i18 (h_150 (M := M)) h_12132 h_12133)
                                let _chain_wd_5439_1 := (let _wd_1_0 := (Litex.powNatReal _value_i18 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_12132 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                                let _wd_1_1 := _value_i18;
                                (Litex.div _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (by
                                    let _litex_power := _atomic_wd_1_0
                                    have _elaborated_power_base := (M.real_subset_complex _ h_12132)
                                    have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                    exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                                  )) (M.real_subset_complex _ h_12132) h_12133))
                                let _chain_wd_5439_2 := _chain_wd_5439_1
                                exact ((by
                                  let _equal_wd_1_0 := _chain_wd_5439_0
                                  let _equal_wd_1_1 := _chain_wd_5439_1
                                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
                                  let _equal_wd_1_0 := _chain_wd_5439_2
                                  exact Litex.Same _equal_wd_1_0 _value_i18))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _chain_wd_5439_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i18 (h_150 (M := M)) h_12132 h_12133)
                                        let _chain_wd_5439_1 := (let _wd_1_0 := (Litex.powNatReal _value_i18 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_12132 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                                        let _wd_1_1 := _value_i18;
                                        (Litex.div _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (by
                                            let _litex_power := _atomic_wd_1_0
                                            have _elaborated_power_base := (M.real_subset_complex _ h_12132)
                                            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                                            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                            exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                                          )) (M.real_subset_complex _ h_12132) h_12133))
                                        let _chain_wd_5439_2 := _chain_wd_5439_1
                                        exact (And.intro (let _equal_wd_1_0 := _chain_wd_5439_0;
                                        let _equal_wd_1_1 := _chain_wd_5439_1;
                                        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i18)) = (M.divValue (M.powValue (Litex.denote _value_i18) (M.number (2 : ℂ))) (Litex.denote _value_i18)) from by
                                          have _litex_residual : (M.divValue (M.powValue (Litex.denote _value_i18) (M.number (2 : ℂ))) (Litex.denote _value_i18)) = (M.divValue (M.powValue (Litex.denote _value_i18) (M.number (2 : ℂ))) (Litex.denote _value_i18)) := (show @Eq M.Value _ _ from Eq.refl _)
                                          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i18)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i18)) = (M.divValue (M.powValue (Litex.denote _value_i18) (M.number (2 : ℂ))) (Litex.denote _value_i18)) from by
                                          let _litex_original := _equal_wd_1_0
                                          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                                          let _wd_1_1 := _value_i18;
                                          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_12132 h_12133))
                                          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_151 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                                          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.powValue _raw_i2 (M.number (2 : ℂ))) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                                          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.powValue _raw_i2 (M.number (2 : ℂ))) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.powValue (Litex.denote _value_i18) (M.number (2 : ℂ))) (Litex.denote _value_i18)) from rfl))
                                        ))).trans _litex_residual))) (let _equal_wd_1_0 := _chain_wd_5439_2;
                                        (show Litex.Same _equal_wd_1_0 _value_i18 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i18 (M.real_subset_complex _ h_12132)) ^ (2 : ℕ)) / (Litex.NativeBridge.asComplex _value_i18 (M.real_subset_complex _ h_12132))) (Litex.NativeBridge.asComplex _value_i18 (M.real_subset_complex _ h_12132)) (Litex.NativeBridge.denoteDiv (_equal_wd_1_0).val.left _value_i18 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denotePowNatReal _value_i18 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_12132 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i18 (M.real_subset_complex _ h_12132))) (Litex.NativeBridge.asComplex_spec _value_i18 (M.real_subset_complex _ h_12132))) (Litex.NativeBridge.asComplex_spec _value_i18 (M.real_subset_complex _ h_12132)) (by
                                          have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i18 (M.real_subset_complex _ h_12132)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i18 (Litex.NativeBridge.asComplex _value_i18 (M.real_subset_complex _ h_12132)) (Litex.NativeBridge.asComplex_spec _value_i18 (M.real_subset_complex _ h_12132)) h_12133
                                          litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                                        ))))))
                                    )
                                )

                              have h_14997 :=
                                (And.left h_5439)

                              have h_14998 :=
                                (And.right h_5439)

                              have h_14999 :=
                                h_14997

                              have h_15000 :=
                                h_14998

                              have h_15001 :=
                                (Eq.trans h_14997 h_14998)
                              let _object_w88 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i18 (h_150 (M := M)) h_12132 h_12133);
                              let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                              (Litex.sub _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (M.real_subset_complex _ (Litex.inOfSame _value_i18 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_15001).symm (show @Eq M.Value _ _ from Eq.refl _) h_12132))) (Litex.numberInC (M := M) (0 : ℂ))))

                              let _object_w89 := (Litex.sub _value_i18 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_12132) (Litex.numberInC (M := M) (0 : ℂ)))

                              have h_5440 : (by
                                let _equal_wd_1_0 := _object_w88
                                let _equal_wd_1_1 := _object_w89
                                exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i18)) = (Litex.denote _value_i18) from h_15001) (show (M.number (0 : ℂ)) = (M.number (0 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))
                                    )
                                )
                              have h_5441 : (by
                                let _chain_wd_5441_0 := (let _wd_1_0 := _object_w88;
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _object_w88
                                  exact (Litex.subInR (_object_w88).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.inOfSame _value_i18 (_object_w88).val.left (Litex.R (M := M)) (Litex.R (M := M)) (h_15001).symm (show @Eq M.Value _ _ from Eq.refl _) h_12132) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                let _chain_wd_5441_1 := (let _wd_1_0 := _object_w89;
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _object_w89
                                  exact (Litex.subInR _value_i18 (Litex.number (M := M) (0 : ℂ)) h_12132 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                exact ((by
                                  let _equal_wd_1_0 := _chain_wd_5441_0
                                  let _equal_wd_1_1 := _chain_wd_5441_1
                                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
                                  let _atomic_wd_1_0 := _chain_wd_5441_1
                                  exact Litex.Lt _atomic_wd_1_0 _value_i9))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _chain_wd_5441_0 := (let _wd_1_0 := _object_w88;
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _object_w88
                                          exact (Litex.subInR (_object_w88).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.inOfSame _value_i18 (_object_w88).val.left (Litex.R (M := M)) (Litex.R (M := M)) (h_15001).symm (show @Eq M.Value _ _ from Eq.refl _) h_12132) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                        let _chain_wd_5441_1 := (let _wd_1_0 := _object_w89;
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _object_w89
                                          exact (Litex.subInR _value_i18 (Litex.number (M := M) (0 : ℂ)) h_12132 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                        exact (And.intro (congrArg (Litex.absValue (M := M)) (show (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i18)) (M.number (0 : ℂ))) = (M.subValue (Litex.denote _value_i18) (M.number (0 : ℂ))) from h_5440)) (by
                                          let _atomic_wd_1_0 := _chain_wd_5441_1
                                          exact h_12119)))
                                    )
                                )

                              have h_15384 :=
                                (And.left h_5441)

                              have h_15385 :=
                                (And.right h_5441)

                              have h_15386 :=
                                h_15384

                              have h_15387 :=
                                h_15385

                              have h_15560 :=
                                (Litex.ltOfSame (let _wd_1_0 := _object_w89;
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _object_w89
                                  exact (Litex.subInR _value_i18 (Litex.number (M := M) (0 : ℂ)) h_12132 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) (let _wd_1_0 := _object_w88;
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _object_w88
                                  exact (Litex.subInR (_object_w88).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.inOfSame _value_i18 (_object_w88).val.left (Litex.R (M := M)) (Litex.R (M := M)) (h_15001).symm (show @Eq M.Value _ _ from Eq.refl _) h_12132) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9 _value_i9 (Eq.symm h_15384) (Litex.sameRefl _value_i9) h_15385)
                              exact (by
                                let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                                let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_15561 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_15561) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_2_0 (by
                                  let _atomic_wd_2_0 := _wd_2_0
                                  exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_15561 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
                                (by
                                  have _preimage_target : (by
                                  let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_16048 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_16048) (Litex.numberInC (M := M) (0 : ℂ)));
                                  (Litex.abs _wd_2_0 (by
                                    let _atomic_wd_3_0 := _wd_2_0
                                    exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_16048 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                  exact Litex.IsSet _atomic_wd_2_0) := (by
                                  let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_16048 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_16048) (Litex.numberInC (M := M) (0 : ℂ)));
                                  (Litex.abs _wd_2_0 (by
                                    let _atomic_wd_3_0 := _wd_2_0
                                    exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_16048 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                  exact (Litex.isSet _atomic_wd_2_0))
                                  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i29 : Litex.Obj (M := M) M.Value) (h_16536 : Litex.In _value_i29 (Litex.R (M := M))) => ∃ (h_16534 : ¬ Litex.Same _value_i29 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i29 (h_150 (M := M)) h_16536 h_16534) _wd_1_1))
                                  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                                exact (by
                                  let _preimage := _atomic_wd_1_1
                                  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i30 : Litex.Obj (M := M) M.Value) (h_17146 : Litex.In _value_i30 (Litex.R (M := M))) => ∃ (h_17144 : ¬ Litex.Same _value_i30 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i30 (h_150 (M := M)) h_17146 h_17144) (_atomic_wd_1_1).val.target))
                                  have _preimage_same : (Litex.denote _value_i18) = (Litex.denote _value_i18) := rfl
                                  exact (Litex.preimageSetMembers _preimage (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _value_i18)).mpr ⟨Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))).domain) _preimage_same) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (Litex.denote _value_i18)).mpr ⟨h_12132, h_12133⟩), Eq.mpr (congrArg (fun x => M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _preimage.val.function) x) (Litex.denote _preimage.val.target)) _preimage_same) (by
                                  let _atomic_wd_2_0 := (_object_w88).val.left
                                  let _atomic_wd_2_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_17726 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_1_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_17726) (Litex.numberInC (M := M) (0 : ℂ)));
                                  (Litex.abs _wd_1_0 (by
                                    let _atomic_wd_3_0 := _wd_1_0
                                    exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_17726 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                  exact (by
                                    let _set := _atomic_wd_2_1
                                    exact (Litex.inSetBuilder_iff _atomic_wd_2_0 _set.val.bound _set.val.predicate).mpr ⟨(by
                                    let _atomic_wd_3_0 := _atomic_wd_2_0
                                    exact (Litex.inOfSame _value_i18 _atomic_wd_3_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_15001).symm (show @Eq M.Value _ _ from Eq.refl _) h_12132)), (by
                                    let _atomic_wd_3_0 := (let _wd_1_0 := _object_w88;
                                    (Litex.abs _wd_1_0 (by
                                      let _atomic_wd_1_0 := _object_w88
                                      exact (Litex.subInR (_object_w88).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.inOfSame _value_i18 (_object_w88).val.left (Litex.R (M := M)) (Litex.R (M := M)) (h_15001).symm (show @Eq M.Value _ _ from Eq.refl _) h_12132) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                    exact (Litex.ltOfSame (let _wd_1_0 := _object_w89;
                                    (Litex.abs _wd_1_0 (by
                                      let _atomic_wd_1_0 := _object_w89
                                      exact (Litex.subInR _value_i18 (Litex.number (M := M) (0 : ℂ)) h_12132 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _atomic_wd_3_0 _value_i9 _value_i9 (h_15384).symm (show @Eq M.Value _ _ from Eq.refl _) h_12119))⟩))⟩))
                            )
                          )
                      )
                    have h_5447 : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24314 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i23 : Litex.Obj (M := M) M.Value) (h_24317 : Litex.In _value_i23 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24314 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ))))) => (by
                        have h_24318 : (M.mem (Litex.denote _value_i23) (M.standard Litex.StandardSetValue.real)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24314 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i23 _litex_builder).mp h_24317)).choose
                              )
                          )
                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i23 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_24318) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_1_0 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.subInR _value_i23 (Litex.number (M := M) (0 : ℂ)) h_24318 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i23 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_24318) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_1_0 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.subInR _value_i23 (Litex.number (M := M) (0 : ℂ)) h_24318 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                      )))
                      let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_25278 : Litex.In _value_i25 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i25 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_25278) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i25 (Litex.number (M := M) (0 : ℂ)) h_25278 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
                      (by
                        have _preimage_target : (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_25541 : Litex.In _value_i25 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i25 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_25541) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i25 (Litex.number (M := M) (0 : ℂ)) h_25541 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                        exact Litex.IsSet _atomic_wd_2_0) := (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_25541 : Litex.In _value_i25 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i25 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_25541) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i25 (Litex.number (M := M) (0 : ℂ)) h_25541 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                        exact (Litex.isSet _atomic_wd_2_0))
                        let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i35 : Litex.Obj (M := M) M.Value) (h_25805 : Litex.In _value_i35 (Litex.R (M := M))) => ∃ (h_25803 : ¬ Litex.Same _value_i35 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i35 (h_150 (M := M)) h_25805 h_25803) _wd_1_1))
                        exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                      exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24314 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i23 : Litex.Obj (M := M) M.Value) (h_24317 : Litex.In _value_i23 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24314 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_24318 : (M.mem (Litex.denote _value_i23) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24314 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i23 _litex_builder).mp h_24317)).choose
                                      )
                                  )
                                exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i23 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_24318) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_2_0 := _wd_1_0
                                  exact (Litex.subInR _value_i23 (Litex.number (M := M) (0 : ℂ)) h_24318 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i23 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_24318) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_2_0 := _wd_1_0
                                  exact (Litex.subInR _value_i23 (Litex.number (M := M) (0 : ℂ)) h_24318 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                              )))
                              let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                              let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_25278 : Litex.In _value_i25 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i25 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_25278) (Litex.numberInC (M := M) (0 : ℂ)));
                              (Litex.abs _wd_2_0 (by
                                let _atomic_wd_2_0 := _wd_2_0
                                exact (Litex.subInR _value_i25 (Litex.number (M := M) (0 : ℂ)) h_25278 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
                              (by
                                have _preimage_target : (by
                                let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_25541 : Litex.In _value_i25 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i25 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_25541) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_2_0 (by
                                  let _atomic_wd_3_0 := _wd_2_0
                                  exact (Litex.subInR _value_i25 (Litex.number (M := M) (0 : ℂ)) h_25541 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                exact Litex.IsSet _atomic_wd_2_0) := (by
                                let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_25541 : Litex.In _value_i25 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i25 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_25541) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_2_0 (by
                                  let _atomic_wd_3_0 := _wd_2_0
                                  exact (Litex.subInR _value_i25 (Litex.number (M := M) (0 : ℂ)) h_25541 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                exact (Litex.isSet _atomic_wd_2_0))
                                let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i35 : Litex.Obj (M := M) M.Value) (h_25805 : Litex.In _value_i35 (Litex.R (M := M))) => ∃ (h_25803 : ¬ Litex.Same _value_i35 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i35 (h_150 (M := M)) h_25805 h_25803) _wd_1_1))
                                exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                              exact (Litex.subsetOfForall _atomic_wd_1_0 _atomic_wd_1_1 (by
                                intro _Host_i33 _rep_i33 _value_i33 h_23178
                                have h_23179 : (M.mem (Litex.denote _value_i33) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i24 : M.Value) => ∃ (_ : M.mem _raw_i24 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i24 = (M.number (0 : ℂ))))))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := _atomic_wd_1_0; (Litex.inSetBuilderObj_iff _value_i33 _litex_builder).mp h_23178)).choose
                                      )
                                  )
                                have h_23182 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i33) (M.number (0 : ℂ)))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i33) (M.number (0 : ℂ)))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r < _s))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := _atomic_wd_1_0; (Litex.inSetBuilderObj_iff _value_i33 _litex_builder).mp h_23178)).choose_spec
                                      )
                                  )
                                have h_23180 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i23 : Litex.Obj (M := M) M.Value) (h_24317 : Litex.In _value_i23 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24314 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ))))) => (by
                                  have h_24318 : (M.mem (Litex.denote _value_i23) (M.standard Litex.StandardSetValue.real)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24314 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i23 _litex_builder).mp h_24317)).choose
                                        )
                                    )
                                  have h_24319 : (¬ ((Litex.denote _value_i23) = (M.number (0 : ℂ)))) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24314 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i23 _litex_builder).mp h_24317)).choose_spec
                                        )
                                    )
                                  exact (let _wd_1_0 := (Litex.sub _value_i23 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_24318) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_2_0 := _wd_1_0
                                  exact (Litex.subInR _value_i23 (Litex.number (M := M) (0 : ℂ)) h_24318 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                )) (Litex.semanticObject (Litex.denote _value_i33) (Litex.isSet _value_i33)) h_23179) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (And.left h_23182)
                                      )
                                  )
                                have h_23181 : Litex.Lt ((fun (_value_i23 : Litex.Obj (M := M) M.Value) (h_24317 : Litex.In _value_i23 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24314 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ))))) => (by
                                  have h_24318 : (M.mem (Litex.denote _value_i23) (M.standard Litex.StandardSetValue.real)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24314 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i23 _litex_builder).mp h_24317)).choose
                                        )
                                    )
                                  have h_24319 : (¬ ((Litex.denote _value_i23) = (M.number (0 : ℂ)))) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24314 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i23 _litex_builder).mp h_24317)).choose_spec
                                        )
                                    )
                                  exact (let _wd_1_0 := (Litex.sub _value_i23 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_24318) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_2_0 := _wd_1_0
                                  exact (Litex.subInR _value_i23 (Litex.number (M := M) (0 : ℂ)) h_24318 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                )) (Litex.semanticObject (Litex.denote _value_i33) (Litex.isSet _value_i33)) h_23179) _value_i9 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (And.right h_23182)
                                      )
                                  )
                                exact (h_5434 _value_i33 h_23178)
                              )))
                          )
                      )
                    have h_27947 : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_27953 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_27956 : Litex.In _value_i15 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_27953 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ))))) => (by
                        have h_27957 : (M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_27953 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i15 _litex_builder).mp h_27956)).choose
                              )
                          )
                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i15 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_27957) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_1_0 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.subInR _value_i15 (Litex.number (M := M) (0 : ℂ)) h_27957 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i15 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_27957) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_1_0 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.subInR _value_i15 (Litex.number (M := M) (0 : ℂ)) h_27957 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                      )))
                      let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_28926 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_28926) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_28926 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
                      (by
                        have _preimage_target : (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_29193 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_29193) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_29193 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                        exact Litex.IsSet _atomic_wd_2_0) := (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_29193 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_29193) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_29193 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                        exact (Litex.isSet _atomic_wd_2_0))
                        let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i37 : Litex.Obj (M := M) M.Value) (h_29461 : Litex.In _value_i37 (Litex.R (M := M))) => ∃ (h_29459 : ¬ Litex.Same _value_i37 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i37 (h_150 (M := M)) h_29461 h_29459) _wd_1_1))
                        exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                      exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) := (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_27953 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_27956 : Litex.In _value_i15 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_27953 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ))))) => (by
                        have h_27957 : (M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_27953 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i15 _litex_builder).mp h_27956)).choose
                              )
                          )
                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i15 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_27957) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_1_0 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.subInR _value_i15 (Litex.number (M := M) (0 : ℂ)) h_27957 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i15 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_27957) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_1_0 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.subInR _value_i15 (Litex.number (M := M) (0 : ℂ)) h_27957 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                      )))
                      let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_28926 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_28926) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_28926 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
                      (by
                        have _preimage_target : (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_29193 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_29193) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_29193 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                        exact Litex.IsSet _atomic_wd_2_0) := (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_29193 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_29193) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_29193 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                        exact (Litex.isSet _atomic_wd_2_0))
                        let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i37 : Litex.Obj (M := M) M.Value) (h_29461 : Litex.In _value_i37 (Litex.R (M := M))) => ∃ (h_29459 : ¬ Litex.Same _value_i37 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i37 (h_150 (M := M)) h_29461 h_29459) _wd_1_1))
                        exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                      exact (Litex.subsetOfSame _atomic_wd_1_0 _atomic_wd_1_1 _atomic_wd_1_0 _atomic_wd_1_1 (by
                        let _left := _atomic_wd_1_0
                        let _right := _atomic_wd_1_0
                        exact (show Litex.Same _left _right from rfl)) (by
                        let _left := _atomic_wd_1_1
                        let _right := _atomic_wd_1_1
                        exact (show Litex.Same _left _right from rfl)) h_5447))
                    exact ⟨_value_i14, h_9047, h_27947⟩
                )
            )
          exact h_5427
        )
      )
  )

theorem h_33384 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) from by
    let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))
    have _limit_function : Litex.In (_object_i1 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_36062 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
  have h_36065 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
  exact Litex.HasFiniteFunctionLimit .both (_object_i1 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) from by
            let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))
            have _limit_function : Litex.In (_object_i1 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
            have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
            have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
            refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
            intro x hx
            exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          )
          have h_36062 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
          have h_36065 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
          exact (by
            let _signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))
            have _member : Litex.In (_object_i1 (M := M)) (Litex.fnSet _signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
            let _source_domain := (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i2 : M.Value) => ∃ (_ : M.mem _raw_i2 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i2 = (M.number (0 : ℂ))))))
            have _domain_set : M.isSet _source_domain := (Litex.SetSemantics.sep_isSet (Litex.denote (Litex.R (M := M))) _ (Litex.isSet (Litex.R (M := M))))
            have _domain_match : _source_domain = _signature.domain := by
              apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
              intro x
              change M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _)
              rw [Litex.SetSemantics.sep_members, Litex.SetSemantics.sep_members]
              exact ⟨fun ⟨hx, _, hg⟩ => ⟨hx, hg⟩, fun ⟨hx, hg⟩ => ⟨hx, hx, hg⟩⟩
            let _domain := Litex.semanticObject _source_domain _domain_set
            exact Litex.finiteFunctionLimitOfForall .both (_object_i1 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _domain _function_limit_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_36062 h_36065 (show ∀ {_Host_i40 : Type _} [_rep_i40 : Litex.Representation M _Host_i40] (_value_i40 : Litex.Obj (M := M) _Host_i40) (h_33412 : Litex.In _value_i40 (Litex.RPos (M := M))), ∃ (_value_i41 : Litex.Obj (M := M) M.Value), ∃ (h_33418 : Litex.In _value_i41 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_33416 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))))), (by
            have h_33419 : (M.mem (Litex.denote _value_i41) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_33416 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i41 _litex_builder).mp h_33418)).choose
                  )
              )
            exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i41 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_33419) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.subInR _value_i41 (Litex.number (M := M) (0 : ℂ)) h_33419 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i41 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_33419) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.subInR _value_i41 (Litex.number (M := M) (0 : ℂ)) h_33419 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i40))
          ) from (by
            intro _Host_i40 _rep_i40 _value_i40 h_33412
            have h_33413 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i40 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_positive _value_i40 h_33412)
                  )
              )
            have h_33414 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i40 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i40 h_33413)
                  )
              )
            have h_33415 : ¬ Litex.Same _value_i40 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i40 h_33413) _litex_zero.symm)
                  )
              )
            exact ((h_157 (M := M)) _value_i40 h_33412)
          )) (show ∀ {_Host_i42 : Type _} [_rep_i42 : Litex.Representation M _Host_i42] (_value_i42 : Litex.Obj (M := M) _Host_i42) (h_34263 : Litex.In _value_i42 (Litex.RPos (M := M))), ∃ (_value_i43 : Litex.Obj (M := M) M.Value), ∃ (h_34267 : Litex.In _value_i43 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_34271 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i44 : Litex.Obj (M := M) M.Value) (h_34274 : Litex.In _value_i44 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_34271 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))))) => (by
            have h_34275 : (M.mem (Litex.denote _value_i44) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_34271 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i44 _litex_builder).mp h_34274)).choose
                  )
              )
            exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i44 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_34275) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.subInR _value_i44 (Litex.number (M := M) (0 : ℂ)) h_34275 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i44 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_34275) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.subInR _value_i44 (Litex.number (M := M) (0 : ℂ)) h_34275 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i43))
          ))) (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i45 : Litex.Obj (M := M) M.Value) (h_35228 : Litex.In _value_i45 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i45 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_35228) (Litex.numberInC (M := M) (0 : ℂ)));
          (Litex.abs _wd_2_0 (by
            let _atomic_wd_2_0 := _wd_2_0
            exact (Litex.subInR _value_i45 (Litex.number (M := M) (0 : ℂ)) h_35228 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i42));
          (by
            have _preimage_target : (by
            let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i45 : Litex.Obj (M := M) M.Value) (h_35484 : Litex.In _value_i45 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i45 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_35484) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_3_0 := _wd_2_0
              exact (Litex.subInR _value_i45 (Litex.number (M := M) (0 : ℂ)) h_35484 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i42))
            exact Litex.IsSet _atomic_wd_2_0) := (by
            let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i45 : Litex.Obj (M := M) M.Value) (h_35484 : Litex.In _value_i45 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i45 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_35484) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_3_0 := _wd_2_0
              exact (Litex.subInR _value_i45 (Litex.number (M := M) (0 : ℂ)) h_35484 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i42))
            exact (Litex.isSet _atomic_wd_2_0))
            let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i46 : Litex.Obj (M := M) M.Value) (h_35741 : Litex.In _value_i46 (Litex.R (M := M))) => ∃ (h_35739 : ¬ Litex.Same _value_i46 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i46 (h_150 (M := M)) h_35741 h_35739) _wd_1_1))
            exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))) from (by
            intro _Host_i42 _rep_i42 _value_i42 h_34263
            have h_34264 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i42 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_positive _value_i42 h_34263)
                  )
              )
            have h_34265 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i42 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i42 h_34264)
                  )
              )
            have h_34266 : ¬ Litex.Same _value_i42 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i42 h_34264) _litex_zero.symm)
                  )
              )
            exact ((h_5420 (M := M)) _value_i42 h_34263)
          ))
          ))
      )
  )

noncomputable def _object_w232 := (let _function := (_object_i1 (M := M)); let _point := (Litex.number (M := M) (0 : ℂ)); Litex.finiteFunctionLimit .both _function _point (show Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) from by
  let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))
  have _limit_function : Litex.In (_object_i1 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
  have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
  have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
  refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
  intro x hx
  exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.finiteFunctionConvergentOfCandidate .both _function _point (Litex.number (M := M) (0 : ℂ)) (h_33384 (M := M))))

theorem h_36076 : (by
  let _equal_wd_1_0 := (_object_w232 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w232 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from ((Litex.finiteFunctionLimitEqCandidate _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (h_33384 (M := M))).trans (show @Eq M.Value _ _ from Eq.refl _))))
      )
  )

noncomputable def _object_w233 := (let _wd_1_0 := (_object_w232 (M := M));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (_object_w232 (M := M))
  exact (M.real_subset_complex _ (Litex.finiteFunctionLimitInR _atomic_wd_1_0))) (Litex.numberInC (M := M) (2 : ℂ))))

theorem h_36093 : (by
  let _equal_wd_1_0 := (_object_w233 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w233 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (by
          let _litex_zero_sum := _equal_wd_1_0
          have _litex_remaining : Litex.Same _litex_zero_sum.val.right (Litex.number (M := M) (2 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
          have _litex_zero : Litex.Same _litex_zero_sum.val.left (Litex.number (M := M) 0) := (h_36076 (M := M))
          have _litex_add_zero_result : Litex.Same _litex_zero_sum (Litex.number (M := M) (2 : ℂ)) := ((congrArg (fun zero_value => M.addValue zero_value (Litex.denote _litex_zero_sum.val.right)) _litex_zero).trans (Litex.zeroAdd _litex_zero_sum.val.right _litex_zero_sum.wd.2)).trans _litex_remaining
          exact _litex_add_zero_result
        )))
      )
  )

theorem h_36141 : (by
  let _atomic_wd_1_0 := (_object_w232 (M := M))
  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w232 (M := M))
          exact (Litex.finiteFunctionLimitInR _atomic_wd_1_0))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_punctured_x5f_cancellation_x2f_statement_x2e_lit
