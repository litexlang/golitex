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
                      let _sign_quotient := _atomic_wd_1_1
                      have _sign_left : Litex.Lt (Litex.number (M := M) 0) _sign_quotient.val.left :=
                        (by
                          have _sign_real := (Litex.inRPos_real _value_i4 h_1006)
                          exact h_1007
                        )
                      have _sign_right : Litex.Lt (Litex.number (M := M) 0) _sign_quotient.val.right :=
                        ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((M.real_members _).mpr ⟨(0 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))⟩) ((M.real_members _).mpr ⟨(2 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))⟩)).mpr (by
                          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) ((M.real_members _).mpr ⟨(0 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))⟩) = (0 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) ((M.real_members _).mpr ⟨(0 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))⟩)).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) ((M.real_members _).mpr ⟨(2 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))⟩) = (2 : ℝ) := by
                            apply Complex.ofReal_injective
                            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) ((M.real_members _).mpr ⟨(2 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))⟩)).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))
                      exact Litex.divPositive _sign_quotient.val.left _sign_quotient.val.right _sign_quotient.wd.1 _sign_quotient.wd.2.1 _sign_quotient.wd.2.2 _sign_left _sign_right
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

          have h_2170 :=
            (And.left h_158)

          have h_2171 :=
            (And.right h_158)

          have h_2172 :=
            h_2170

          have h_2173 :=
            h_2171

          have h_2266 :=
            (Litex.ltTrans (Litex.number (M := M) (0 : ℂ)) (Litex.div _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i4 h_1006) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) _value_i4 h_2170 h_2171)
          let _object_w15 := (Litex.div _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.positiveRealToComplex _value_i4 h_1006) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

          have h_159 : (by
            let _atomic_wd_1_0 := _object_w15
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w15
                    exact (fun _litex_equal => (Litex.ltNotSame (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0 h_2170) _litex_equal.symm))
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
                      exact h_2170)))
                    )))))
                )
            )

          have h_2844 :=
            (And.left h_161)

          have h_2845 :=
            (And.right h_161)

          have h_2846 :=
            h_2844

          have h_2847 :=
            h_2845

          have h_2848 :=
            (Eq.trans h_2844 h_2845)
          have h_166 : ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_2852 : Litex.In _value_i7 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_2849 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ))))), (by
            have h_2853 : (M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_2849 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i7 _litex_builder).mp h_2852)).choose
                  )
              )
            exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i7 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_2853) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i7 (Litex.number (M := M) (0 : ℂ)) h_2853 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i7 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_2853) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i7 (Litex.number (M := M) (0 : ℂ)) h_2853 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i4))
          ) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i7 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _object_w15) (Litex.isSet _object_w15)
                    have h_3740 : Litex.In _value_i7 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_3737 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)))) := (by
                      let _atomic_wd_1_0 := _object_w15
                      let _atomic_wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_3695 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ))))
                      exact (by
                        let _set := _atomic_wd_1_1
                        exact (Litex.inSetBuilder_iff _atomic_wd_1_0 _set.val.bound _set.val.predicate).mpr ⟨(by
                        let _atomic_wd_2_0 := _object_w15
                        exact (Litex.divInR _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.inRPos_real _value_i4 h_1006) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (_atomic_wd_2_0).wd.2.2)), (by
                        let _atomic_wd_2_0 := _object_w15
                        exact h_159)⟩))
                    have h_3741 : (M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_3737 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i7 _litex_builder).mp h_3740)).choose
                          )
                      )
                    have h_3742 : (¬ ((Litex.denote _value_i7) = (M.number (0 : ℂ)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_3737 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i7 _litex_builder).mp h_3740)).choose_spec
                          )
                      )
                    have h_3743 : Litex.Same _value_i7 (_object_w16).val.left := rfl
                    have h_3746 : ((by
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
                      exact (Litex.ltOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_object_w16).val.left _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (h_2848).symm h_2170)) (by
                      let _atomic_wd_1_0 := (let _wd_1_0 := _object_w16;
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _object_w16
                        exact (Litex.subInR (_object_w16).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.divInR _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.inRPos_real _value_i4 h_1006) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) ((_object_w16).val.left).wd.2.2) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                      exact (Litex.ltOfSame (_object_w16).val.left _atomic_wd_1_0 _value_i4 _value_i4 (h_2848).symm (show @Eq M.Value _ _ from Eq.refl _) h_2171)))
                    exact ⟨_value_i7, h_3740, h_3746⟩
                )
            )
          exact h_166
        )
      )
  )

theorem h_5453 : ∀ {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_5481 : Litex.In _value_i9 (Litex.RPos (M := M))), ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_5485 : Litex.In _value_i10 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_5489 : Litex.In _value_i12 (Litex.R (M := M))) => ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_5492 : Litex.In _value_i11 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_5489 : Litex.In _value_i12 (Litex.R (M := M))) => ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ))))) => (by
  have h_5493 : (M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_5489 : Litex.In _value_i12 (Litex.R (M := M))) => ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i11 _litex_builder).mp h_5492)).choose
        )
    )
  exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i11 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_5493) (Litex.numberInC (M := M) (0 : ℂ)));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i11 (Litex.number (M := M) (0 : ℂ)) h_5493 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i11 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_5493) (Litex.numberInC (M := M) (0 : ℂ)));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i11 (Litex.number (M := M) (0 : ℂ)) h_5493 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i10))
))) (let _wd_1_0 := (_object_i1 (M := M));
let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_6446 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i13 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_6446) (Litex.numberInC (M := M) (0 : ℂ)));
(Litex.abs _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.subInR _value_i13 (Litex.number (M := M) (0 : ℂ)) h_6446 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
(by
  have _preimage_target : (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_6702 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i13 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_6702) (Litex.numberInC (M := M) (0 : ℂ)));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i13 (Litex.number (M := M) (0 : ℂ)) h_6702 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
  exact Litex.IsSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_6702 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i13 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_6702) (Litex.numberInC (M := M) (0 : ℂ)));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i13 (Litex.number (M := M) (0 : ℂ)) h_6702 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
  exact (Litex.isSet _atomic_wd_1_0))
  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i26 : Litex.Obj (M := M) M.Value) (h_6959 : Litex.In _value_i26 (Litex.R (M := M))) => ∃ (h_6957 : ¬ Litex.Same _value_i26 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i26 (h_150 (M := M)) h_6959 h_6957) _wd_1_1))
  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_5481
          have h_5482 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i9 h_5481)
                )
            )
          have h_5483 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_5482)
                )
            )
          have h_5484 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_5482) _litex_zero.symm)
                )
            )
          have h_7278 : Litex.In _value_i9 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5481
                )
            )
          have h_7279 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i9 h_7278)
                )
            )
          have h_7280 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_7279)
                )
            )
          have h_7281 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_7279) _litex_zero.symm)
                )
            )
          have h_5460 : ∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (h_7282 : Litex.In _value_i14 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_7286 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_7289 : Litex.In _value_i15 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_7286 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ))))) => (by
            have h_7290 : (M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_7286 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i15 _litex_builder).mp h_7289)).choose
                  )
              )
            exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i15 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_7290) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i15 (Litex.number (M := M) (0 : ℂ)) h_7290 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i15 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_7290) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i15 (Litex.number (M := M) (0 : ℂ)) h_7290 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i14))
          ))) (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_8243 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_8243) (Litex.numberInC (M := M) (0 : ℂ)));
          (Litex.abs _wd_2_0 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_8243 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
          (by
            have _preimage_target : (by
            let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_8499 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_8499) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_8499 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
            exact Litex.IsSet _atomic_wd_1_0) := (by
            let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_8499 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_8499) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_8499 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
            exact (Litex.isSet _atomic_wd_1_0))
            let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i27 : Litex.Obj (M := M) M.Value) (h_8756 : Litex.In _value_i27 (Litex.R (M := M))) => ∃ (h_8754 : ¬ Litex.Same _value_i27 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i27 (h_150 (M := M)) h_8756 h_8754) _wd_1_1))
            exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i14 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)
                    have h_9080 : Litex.In _value_i14 (Litex.RPos (M := M)) := h_7278
                    have h_9081 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i14 h_9080)
                          )
                      )
                    have h_9082 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_9081)
                          )
                      )
                    have h_9083 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_9081) _litex_zero.symm)
                          )
                      )
                    have h_9084 : Litex.Same _value_i14 _value_i9 := rfl
                    have h_5467 : ∀ {_Host_i18 : Type _} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_10049 : Litex.In _value_i18 (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_9088 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                      have h_9089 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9088)).choose
                            )
                        )
                      exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9089) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9089 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9089) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9089 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                    )))), Litex.In _value_i18 (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_10054 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_10054) (Litex.numberInC (M := M) (0 : ℂ)));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_10054 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
                    (by
                      have _preimage_target : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_10407 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_10407) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_10407 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                      exact Litex.IsSet _atomic_wd_1_0) := (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_10407 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_10407) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_10407 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                      exact (Litex.isSet _atomic_wd_1_0))
                      let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i28 : Litex.Obj (M := M) M.Value) (h_10761 : Litex.In _value_i28 (Litex.R (M := M))) => ∃ (h_10759 : ¬ Litex.Same _value_i28 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i28 (h_150 (M := M)) h_10761 h_10759) _wd_1_1))
                      exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i18 _rep_i18 _value_i18 h_10049
                              have h_10050 : (M.mem (Litex.denote _value_i18) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i20 : M.Value) => ∃ (_ : M.mem _raw_i20 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i20 = (M.number (0 : ℂ))))))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_9088 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                        have h_9089 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                          (by
                                            litex_checked_step =>
                                              exact (
                                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9088)).choose
                                              )
                                          )
                                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9089) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9089 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9089) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9089 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                      ))); (Litex.inSetBuilderObj_iff _value_i18 _litex_builder).mp h_10049)).choose
                                    )
                                )
                              have h_10053 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i18) (M.number (0 : ℂ)))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i18) (M.number (0 : ℂ)))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r < _s))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_9088 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                        have h_9089 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                          (by
                                            litex_checked_step =>
                                              exact (
                                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9088)).choose
                                              )
                                          )
                                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9089) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9089 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9089) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9089 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                      ))); (Litex.inSetBuilderObj_iff _value_i18 _litex_builder).mp h_10049)).choose_spec
                                    )
                                )
                              have h_10051 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_9088 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_9089 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9088)).choose
                                      )
                                  )
                                have h_9090 : (¬ ((Litex.denote _value_i19) = (M.number (0 : ℂ)))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9088)).choose_spec
                                      )
                                  )
                                exact (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9089) (Litex.numberInC (M := M) (0 : ℂ)));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9089 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                              )) (Litex.semanticObject (Litex.denote _value_i18) (Litex.isSet _value_i18)) h_10050) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.left h_10053)
                                    )
                                )
                              have h_10052 : Litex.Lt ((fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_9088 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_9089 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9088)).choose
                                      )
                                  )
                                have h_9090 : (¬ ((Litex.denote _value_i19) = (M.number (0 : ℂ)))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9085 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_9088)).choose_spec
                                      )
                                  )
                                exact (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_9089) (Litex.numberInC (M := M) (0 : ℂ)));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_9089 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                              )) (Litex.semanticObject (Litex.denote _value_i18) (Litex.isSet _value_i18)) h_10050) _value_i9 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.right h_10053)
                                    )
                                )
                              have h_12149 : Litex.In _value_i18 (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_11188 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_11189 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11188)).choose
                                      )
                                  )
                                exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11189) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11189 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11189) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11189 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                              ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_10049
                                    )
                                )
                              have h_12150 : (M.mem (Litex.denote _value_i18) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i20 : M.Value) => ∃ (_ : M.mem _raw_i20 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i20 = (M.number (0 : ℂ))))))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_11188 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                        have h_11189 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                          (by
                                            litex_checked_step =>
                                              exact (
                                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11188)).choose
                                              )
                                          )
                                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11189) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11189 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11189) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11189 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                      ))); (Litex.inSetBuilderObj_iff _value_i18 _litex_builder).mp h_12149)).choose
                                    )
                                )
                              have h_12153 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i18) (M.number (0 : ℂ)))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i18) (M.number (0 : ℂ)))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r < _s))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_11188 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                        have h_11189 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                          (by
                                            litex_checked_step =>
                                              exact (
                                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11188)).choose
                                              )
                                          )
                                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11189) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11189 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11189) (Litex.numberInC (M := M) (0 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11189 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                      ))); (Litex.inSetBuilderObj_iff _value_i18 _litex_builder).mp h_12149)).choose_spec
                                    )
                                )
                              have h_12151 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_11188 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_11189 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11188)).choose
                                      )
                                  )
                                have h_11190 : (¬ ((Litex.denote _value_i19) = (M.number (0 : ℂ)))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11188)).choose_spec
                                      )
                                  )
                                exact (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11189) (Litex.numberInC (M := M) (0 : ℂ)));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11189 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                              )) (Litex.semanticObject (Litex.denote _value_i18) (Litex.isSet _value_i18)) h_12150) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.left h_12153)
                                    )
                                )
                              have h_12152 : Litex.Lt ((fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_11188 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_11189 : (M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11188)).choose
                                      )
                                  )
                                have h_11190 : (¬ ((Litex.denote _value_i19) = (M.number (0 : ℂ)))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_11185 : Litex.In _value_i20 (Litex.R (M := M))) => ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i19 _litex_builder).mp h_11188)).choose_spec
                                      )
                                  )
                                exact (let _wd_1_0 := (Litex.sub _value_i19 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_11189) (Litex.numberInC (M := M) (0 : ℂ)));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i19 (Litex.number (M := M) (0 : ℂ)) h_11189 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                              )) (Litex.semanticObject (Litex.denote _value_i18) (Litex.isSet _value_i18)) h_12150) _value_i9 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.right h_12153)
                                    )
                                )
                              let _object_w85 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i22 : Litex.Obj (M := M) M.Value) (h_12154 : Litex.In _value_i22 (Litex.R (M := M))) => ¬ Litex.Same _value_i22 (Litex.number (M := M) (0 : ℂ))))

                              have h_5469 : (by
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
                                          exact (show Litex.Same _left _right from rfl)) h_12150))
                                    )
                                )

                              have h_12165 : (M.mem (Litex.denote _value_i18) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := _object_w85; (Litex.inSetBuilderObj_iff _value_i18 _litex_builder).mp h_5469)).choose
                                    )
                                )

                              have h_12166 : (¬ ((Litex.denote _value_i18) = (M.number (0 : ℂ)))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := _object_w85; (Litex.inSetBuilderObj_iff _value_i18 _litex_builder).mp h_5469)).choose_spec
                                    )
                                )
                              have h_5470 : Litex.In _value_i18 (Litex.R (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_12165
                                    )
                                )
                              have h_5471 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_12166
                                    )
                                )
                              have h_5472 : (by
                                let _chain_wd_5472_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i18 (h_150 (M := M)) h_12165 h_12166)
                                let _chain_wd_5472_1 := (let _wd_1_0 := (Litex.powNatReal _value_i18 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_12165 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                                let _wd_1_1 := _value_i18;
                                (Litex.div _wd_1_0 _wd_1_1 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (by
                                    let _litex_power := _atomic_wd_1_0
                                    have _elaborated_power_base := (M.real_subset_complex _ h_12165)
                                    have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                    exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                                  )) (M.real_subset_complex _ h_12165) h_12166))
                                let _chain_wd_5472_2 := _chain_wd_5472_1
                                exact ((by
                                  let _equal_wd_1_0 := _chain_wd_5472_0
                                  let _equal_wd_1_1 := _chain_wd_5472_1
                                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
                                  let _equal_wd_1_0 := _chain_wd_5472_2
                                  exact Litex.Same _equal_wd_1_0 _value_i18))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _chain_wd_5472_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i18 (h_150 (M := M)) h_12165 h_12166)
                                        let _chain_wd_5472_1 := (let _wd_1_0 := (Litex.powNatReal _value_i18 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_12165 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                                        let _wd_1_1 := _value_i18;
                                        (Litex.div _wd_1_0 _wd_1_1 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (by
                                            let _litex_power := _atomic_wd_1_0
                                            have _elaborated_power_base := (M.real_subset_complex _ h_12165)
                                            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
                                            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                            exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
                                          )) (M.real_subset_complex _ h_12165) h_12166))
                                        let _chain_wd_5472_2 := _chain_wd_5472_1
                                        exact (And.intro (let _equal_wd_1_0 := _chain_wd_5472_0;
                                        let _equal_wd_1_1 := _chain_wd_5472_1;
                                        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i18)) = (M.divValue (M.powValue (Litex.denote _value_i18) (M.number (2 : ℂ))) (Litex.denote _value_i18)) from by
                                          have _litex_residual : (M.divValue (M.powValue (Litex.denote _value_i18) (M.number (2 : ℂ))) (Litex.denote _value_i18)) = (M.divValue (M.powValue (Litex.denote _value_i18) (M.number (2 : ℂ))) (Litex.denote _value_i18)) := (show @Eq M.Value _ _ from Eq.refl _)
                                          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i18)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i18)) = (M.divValue (M.powValue (Litex.denote _value_i18) (M.number (2 : ℂ))) (Litex.denote _value_i18)) from by
                                          let _litex_original := _equal_wd_1_0
                                          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                                          let _wd_1_1 := _value_i18;
                                          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_12165 h_12166))
                                          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_151 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                                          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.powValue _raw_i2 (M.number (2 : ℂ))) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                                          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.powValue _raw_i2 (M.number (2 : ℂ))) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.powValue (Litex.denote _value_i18) (M.number (2 : ℂ))) (Litex.denote _value_i18)) from rfl))
                                        ))).trans _litex_residual))) (let _equal_wd_1_0 := _chain_wd_5472_2;
                                        (show Litex.Same _equal_wd_1_0 _value_i18 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i18 (M.real_subset_complex _ h_12165)) ^ (2 : ℕ)) / (Litex.NativeBridge.asComplex _value_i18 (M.real_subset_complex _ h_12165))) (Litex.NativeBridge.asComplex _value_i18 (M.real_subset_complex _ h_12165)) (Litex.NativeBridge.denoteDiv (_equal_wd_1_0).val.left _value_i18 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denotePowNatReal _value_i18 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_12165 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i18 (M.real_subset_complex _ h_12165))) (Litex.NativeBridge.asComplex_spec _value_i18 (M.real_subset_complex _ h_12165))) (Litex.NativeBridge.asComplex_spec _value_i18 (M.real_subset_complex _ h_12165)) (by
                                          have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i18 (M.real_subset_complex _ h_12165)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i18 (Litex.NativeBridge.asComplex _value_i18 (M.real_subset_complex _ h_12165)) (Litex.NativeBridge.asComplex_spec _value_i18 (M.real_subset_complex _ h_12165)) h_12166
                                          litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                                        ))))))
                                    )
                                )

                              have h_15030 :=
                                (And.left h_5472)

                              have h_15031 :=
                                (And.right h_5472)

                              have h_15032 :=
                                h_15030

                              have h_15033 :=
                                h_15031

                              have h_15034 :=
                                (Eq.trans h_15030 h_15031)
                              let _object_w88 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i18 (h_150 (M := M)) h_12165 h_12166);
                              let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
                              (Litex.sub _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (M.real_subset_complex _ (Litex.inOfSame _value_i18 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_15034).symm (show @Eq M.Value _ _ from Eq.refl _) h_12165))) (Litex.numberInC (M := M) (0 : ℂ))))

                              let _object_w89 := (Litex.sub _value_i18 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_12165) (Litex.numberInC (M := M) (0 : ℂ)))

                              have h_5473 : (by
                                let _equal_wd_1_0 := _object_w88
                                let _equal_wd_1_1 := _object_w89
                                exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i18)) = (Litex.denote _value_i18) from h_15034) (show (M.number (0 : ℂ)) = (M.number (0 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))
                                    )
                                )
                              have h_5474 : (by
                                let _chain_wd_5474_0 := (let _wd_1_0 := _object_w88;
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _object_w88
                                  exact (Litex.subInR (_object_w88).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.inOfSame _value_i18 (_object_w88).val.left (Litex.R (M := M)) (Litex.R (M := M)) (h_15034).symm (show @Eq M.Value _ _ from Eq.refl _) h_12165) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                let _chain_wd_5474_1 := (let _wd_1_0 := _object_w89;
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _object_w89
                                  exact (Litex.subInR _value_i18 (Litex.number (M := M) (0 : ℂ)) h_12165 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                exact ((by
                                  let _equal_wd_1_0 := _chain_wd_5474_0
                                  let _equal_wd_1_1 := _chain_wd_5474_1
                                  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
                                  let _atomic_wd_1_0 := _chain_wd_5474_1
                                  exact Litex.Lt _atomic_wd_1_0 _value_i9))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _chain_wd_5474_0 := (let _wd_1_0 := _object_w88;
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _object_w88
                                          exact (Litex.subInR (_object_w88).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.inOfSame _value_i18 (_object_w88).val.left (Litex.R (M := M)) (Litex.R (M := M)) (h_15034).symm (show @Eq M.Value _ _ from Eq.refl _) h_12165) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                        let _chain_wd_5474_1 := (let _wd_1_0 := _object_w89;
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _object_w89
                                          exact (Litex.subInR _value_i18 (Litex.number (M := M) (0 : ℂ)) h_12165 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                        exact (And.intro (congrArg (Litex.absValue (M := M)) (show (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i18)) (M.number (0 : ℂ))) = (M.subValue (Litex.denote _value_i18) (M.number (0 : ℂ))) from h_5473)) (by
                                          let _atomic_wd_1_0 := _chain_wd_5474_1
                                          exact h_12152)))
                                    )
                                )

                              have h_15417 :=
                                (And.left h_5474)

                              have h_15418 :=
                                (And.right h_5474)

                              have h_15419 :=
                                h_15417

                              have h_15420 :=
                                h_15418

                              have h_15593 :=
                                (Litex.ltOfSame (let _wd_1_0 := _object_w89;
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _object_w89
                                  exact (Litex.subInR _value_i18 (Litex.number (M := M) (0 : ℂ)) h_12165 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) (let _wd_1_0 := _object_w88;
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _object_w88
                                  exact (Litex.subInR (_object_w88).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.inOfSame _value_i18 (_object_w88).val.left (Litex.R (M := M)) (Litex.R (M := M)) (h_15034).symm (show @Eq M.Value _ _ from Eq.refl _) h_12165) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9 _value_i9 (Eq.symm h_15417) (Litex.sameRefl _value_i9) h_15418)
                              exact (by
                                let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                                let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_15594 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_15594) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_2_0 (by
                                  let _atomic_wd_2_0 := _wd_2_0
                                  exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_15594 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
                                (by
                                  have _preimage_target : (by
                                  let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_16081 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_16081) (Litex.numberInC (M := M) (0 : ℂ)));
                                  (Litex.abs _wd_2_0 (by
                                    let _atomic_wd_3_0 := _wd_2_0
                                    exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_16081 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                  exact Litex.IsSet _atomic_wd_2_0) := (by
                                  let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_16081 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_16081) (Litex.numberInC (M := M) (0 : ℂ)));
                                  (Litex.abs _wd_2_0 (by
                                    let _atomic_wd_3_0 := _wd_2_0
                                    exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_16081 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                  exact (Litex.isSet _atomic_wd_2_0))
                                  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i29 : Litex.Obj (M := M) M.Value) (h_16569 : Litex.In _value_i29 (Litex.R (M := M))) => ∃ (h_16567 : ¬ Litex.Same _value_i29 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i29 (h_150 (M := M)) h_16569 h_16567) _wd_1_1))
                                  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                                exact (by
                                  let _preimage := _atomic_wd_1_1
                                  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i30 : Litex.Obj (M := M) M.Value) (h_17179 : Litex.In _value_i30 (Litex.R (M := M))) => ∃ (h_17177 : ¬ Litex.Same _value_i30 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i30 (h_150 (M := M)) h_17179 h_17177) (_atomic_wd_1_1).val.target))
                                  have _preimage_same : (Litex.denote _value_i18) = (Litex.denote _value_i18) := rfl
                                  exact (Litex.preimageSetMembers _preimage (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _value_i18)).mpr ⟨Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))).domain) _preimage_same) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (Litex.denote _value_i18)).mpr ⟨h_12165, h_12166⟩), Eq.mpr (congrArg (fun x => M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _preimage.val.function) x) (Litex.denote _preimage.val.target)) _preimage_same) (by
                                  let _atomic_wd_2_0 := (_object_w88).val.left
                                  let _atomic_wd_2_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_17759 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_1_0 := (Litex.sub _value_i21 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_17759) (Litex.numberInC (M := M) (0 : ℂ)));
                                  (Litex.abs _wd_1_0 (by
                                    let _atomic_wd_3_0 := _wd_1_0
                                    exact (Litex.subInR _value_i21 (Litex.number (M := M) (0 : ℂ)) h_17759 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                  exact (by
                                    let _set := _atomic_wd_2_1
                                    exact (Litex.inSetBuilder_iff _atomic_wd_2_0 _set.val.bound _set.val.predicate).mpr ⟨(by
                                    let _atomic_wd_3_0 := _atomic_wd_2_0
                                    exact (Litex.inOfSame _value_i18 _atomic_wd_3_0 (Litex.R (M := M)) (Litex.R (M := M)) (h_15034).symm (show @Eq M.Value _ _ from Eq.refl _) h_12165)), (by
                                    let _atomic_wd_3_0 := (let _wd_1_0 := _object_w88;
                                    (Litex.abs _wd_1_0 (by
                                      let _atomic_wd_1_0 := _object_w88
                                      exact (Litex.subInR (_object_w88).val.left (Litex.number (M := M) (0 : ℂ)) (Litex.inOfSame _value_i18 (_object_w88).val.left (Litex.R (M := M)) (Litex.R (M := M)) (h_15034).symm (show @Eq M.Value _ _ from Eq.refl _) h_12165) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                    exact (Litex.ltOfSame (let _wd_1_0 := _object_w89;
                                    (Litex.abs _wd_1_0 (by
                                      let _atomic_wd_1_0 := _object_w89
                                      exact (Litex.subInR _value_i18 (Litex.number (M := M) (0 : ℂ)) h_12165 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _atomic_wd_3_0 _value_i9 _value_i9 (h_15417).symm (show @Eq M.Value _ _ from Eq.refl _) h_12152))⟩))⟩))
                            )
                          )
                      )
                    have h_5480 : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24347 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i23 : Litex.Obj (M := M) M.Value) (h_24350 : Litex.In _value_i23 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24347 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ))))) => (by
                        have h_24351 : (M.mem (Litex.denote _value_i23) (M.standard Litex.StandardSetValue.real)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24347 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i23 _litex_builder).mp h_24350)).choose
                              )
                          )
                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i23 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_24351) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_1_0 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.subInR _value_i23 (Litex.number (M := M) (0 : ℂ)) h_24351 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i23 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_24351) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_1_0 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.subInR _value_i23 (Litex.number (M := M) (0 : ℂ)) h_24351 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                      )))
                      let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_25311 : Litex.In _value_i25 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i25 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_25311) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i25 (Litex.number (M := M) (0 : ℂ)) h_25311 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
                      (by
                        have _preimage_target : (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_25574 : Litex.In _value_i25 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i25 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_25574) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i25 (Litex.number (M := M) (0 : ℂ)) h_25574 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                        exact Litex.IsSet _atomic_wd_2_0) := (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_25574 : Litex.In _value_i25 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i25 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_25574) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i25 (Litex.number (M := M) (0 : ℂ)) h_25574 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                        exact (Litex.isSet _atomic_wd_2_0))
                        let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i35 : Litex.Obj (M := M) M.Value) (h_25838 : Litex.In _value_i35 (Litex.R (M := M))) => ∃ (h_25836 : ¬ Litex.Same _value_i35 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i35 (h_150 (M := M)) h_25838 h_25836) _wd_1_1))
                        exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                      exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24347 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i23 : Litex.Obj (M := M) M.Value) (h_24350 : Litex.In _value_i23 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24347 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_24351 : (M.mem (Litex.denote _value_i23) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24347 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i23 _litex_builder).mp h_24350)).choose
                                      )
                                  )
                                exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i23 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_24351) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_2_0 := _wd_1_0
                                  exact (Litex.subInR _value_i23 (Litex.number (M := M) (0 : ℂ)) h_24351 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i23 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_24351) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_2_0 := _wd_1_0
                                  exact (Litex.subInR _value_i23 (Litex.number (M := M) (0 : ℂ)) h_24351 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                              )))
                              let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                              let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_25311 : Litex.In _value_i25 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i25 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_25311) (Litex.numberInC (M := M) (0 : ℂ)));
                              (Litex.abs _wd_2_0 (by
                                let _atomic_wd_2_0 := _wd_2_0
                                exact (Litex.subInR _value_i25 (Litex.number (M := M) (0 : ℂ)) h_25311 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
                              (by
                                have _preimage_target : (by
                                let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_25574 : Litex.In _value_i25 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i25 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_25574) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_2_0 (by
                                  let _atomic_wd_3_0 := _wd_2_0
                                  exact (Litex.subInR _value_i25 (Litex.number (M := M) (0 : ℂ)) h_25574 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                exact Litex.IsSet _atomic_wd_2_0) := (by
                                let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i25 : Litex.Obj (M := M) M.Value) (h_25574 : Litex.In _value_i25 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i25 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_25574) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_2_0 (by
                                  let _atomic_wd_3_0 := _wd_2_0
                                  exact (Litex.subInR _value_i25 (Litex.number (M := M) (0 : ℂ)) h_25574 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                                exact (Litex.isSet _atomic_wd_2_0))
                                let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i35 : Litex.Obj (M := M) M.Value) (h_25838 : Litex.In _value_i35 (Litex.R (M := M))) => ∃ (h_25836 : ¬ Litex.Same _value_i35 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i35 (h_150 (M := M)) h_25838 h_25836) _wd_1_1))
                                exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                              exact (Litex.subsetOfForall _atomic_wd_1_0 _atomic_wd_1_1 (by
                                intro _Host_i33 _rep_i33 _value_i33 h_23211
                                have h_23212 : (M.mem (Litex.denote _value_i33) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i24 : M.Value) => ∃ (_ : M.mem _raw_i24 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i24 = (M.number (0 : ℂ))))))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := _atomic_wd_1_0; (Litex.inSetBuilderObj_iff _value_i33 _litex_builder).mp h_23211)).choose
                                      )
                                  )
                                have h_23215 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i33) (M.number (0 : ℂ)))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i33) (M.number (0 : ℂ)))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r < _s))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := _atomic_wd_1_0; (Litex.inSetBuilderObj_iff _value_i33 _litex_builder).mp h_23211)).choose_spec
                                      )
                                  )
                                have h_23213 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i23 : Litex.Obj (M := M) M.Value) (h_24350 : Litex.In _value_i23 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24347 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ))))) => (by
                                  have h_24351 : (M.mem (Litex.denote _value_i23) (M.standard Litex.StandardSetValue.real)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24347 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i23 _litex_builder).mp h_24350)).choose
                                        )
                                    )
                                  have h_24352 : (¬ ((Litex.denote _value_i23) = (M.number (0 : ℂ)))) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24347 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i23 _litex_builder).mp h_24350)).choose_spec
                                        )
                                    )
                                  exact (let _wd_1_0 := (Litex.sub _value_i23 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_24351) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_2_0 := _wd_1_0
                                  exact (Litex.subInR _value_i23 (Litex.number (M := M) (0 : ℂ)) h_24351 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                )) (Litex.semanticObject (Litex.denote _value_i33) (Litex.isSet _value_i33)) h_23212) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (And.left h_23215)
                                      )
                                  )
                                have h_23214 : Litex.Lt ((fun (_value_i23 : Litex.Obj (M := M) M.Value) (h_24350 : Litex.In _value_i23 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24347 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ))))) => (by
                                  have h_24351 : (M.mem (Litex.denote _value_i23) (M.standard Litex.StandardSetValue.real)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24347 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i23 _litex_builder).mp h_24350)).choose
                                        )
                                    )
                                  have h_24352 : (¬ ((Litex.denote _value_i23) = (M.number (0 : ℂ)))) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_24347 : Litex.In _value_i24 (Litex.R (M := M))) => ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i23 _litex_builder).mp h_24350)).choose_spec
                                        )
                                    )
                                  exact (let _wd_1_0 := (Litex.sub _value_i23 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_24351) (Litex.numberInC (M := M) (0 : ℂ)));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_2_0 := _wd_1_0
                                  exact (Litex.subInR _value_i23 (Litex.number (M := M) (0 : ℂ)) h_24351 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))
                                )) (Litex.semanticObject (Litex.denote _value_i33) (Litex.isSet _value_i33)) h_23212) _value_i9 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (And.right h_23215)
                                      )
                                  )
                                exact (h_5467 (Litex.semanticObject (Litex.denote _value_i33) (Litex.isSet _value_i33)) h_23211)
                              )))
                          )
                      )
                    have h_27980 : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_27986 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_27989 : Litex.In _value_i15 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_27986 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ))))) => (by
                        have h_27990 : (M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_27986 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i15 _litex_builder).mp h_27989)).choose
                              )
                          )
                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i15 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_27990) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_1_0 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.subInR _value_i15 (Litex.number (M := M) (0 : ℂ)) h_27990 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i15 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_27990) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_1_0 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.subInR _value_i15 (Litex.number (M := M) (0 : ℂ)) h_27990 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                      )))
                      let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_28959 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_28959) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_28959 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
                      (by
                        have _preimage_target : (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_29226 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_29226) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_29226 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                        exact Litex.IsSet _atomic_wd_2_0) := (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_29226 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_29226) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_29226 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                        exact (Litex.isSet _atomic_wd_2_0))
                        let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i37 : Litex.Obj (M := M) M.Value) (h_29494 : Litex.In _value_i37 (Litex.R (M := M))) => ∃ (h_29492 : ¬ Litex.Same _value_i37 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i37 (h_150 (M := M)) h_29494 h_29492) _wd_1_1))
                        exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                      exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) := (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_27986 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_27989 : Litex.In _value_i15 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_27986 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ))))) => (by
                        have h_27990 : (M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_27986 : Litex.In _value_i16 (Litex.R (M := M))) => ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i15 _litex_builder).mp h_27989)).choose
                              )
                          )
                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i15 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_27990) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_1_0 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.subInR _value_i15 (Litex.number (M := M) (0 : ℂ)) h_27990 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i15 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_27990) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_1_0 (by
                          let _atomic_wd_2_0 := _wd_1_0
                          exact (Litex.subInR _value_i15 (Litex.number (M := M) (0 : ℂ)) h_27990 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                      )))
                      let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_28959 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_28959) (Litex.numberInC (M := M) (0 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_28959 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9));
                      (by
                        have _preimage_target : (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_29226 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_29226) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_29226 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                        exact Litex.IsSet _atomic_wd_2_0) := (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_29226 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_29226) (Litex.numberInC (M := M) (0 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i17 (Litex.number (M := M) (0 : ℂ)) h_29226 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i9))
                        exact (Litex.isSet _atomic_wd_2_0))
                        let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i37 : Litex.Obj (M := M) M.Value) (h_29494 : Litex.In _value_i37 (Litex.R (M := M))) => ∃ (h_29492 : ¬ Litex.Same _value_i37 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i37 (h_150 (M := M)) h_29494 h_29492) _wd_1_1))
                        exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                      exact (Litex.subsetOfSame _atomic_wd_1_0 _atomic_wd_1_1 _atomic_wd_1_0 _atomic_wd_1_1 (by
                        let _left := _atomic_wd_1_0
                        let _right := _atomic_wd_1_0
                        exact (show Litex.Same _left _right from rfl)) (by
                        let _left := _atomic_wd_1_1
                        let _right := _atomic_wd_1_1
                        exact (show Litex.Same _left _right from rfl)) h_5480))
                    exact ⟨_value_i14, h_9080, h_27980⟩
                )
            )
          exact h_5460
        )
      )
  )

theorem h_33417 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) from by
    let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))
    have _limit_function : Litex.In (_object_i1 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_36095 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
  have h_36098 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
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
          have h_36095 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
          have h_36098 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
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
            exact Litex.finiteFunctionLimitOfForall .both (_object_i1 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _domain _function_limit_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_36095 h_36098 (show ∀ {_Host_i40 : Type _} [_rep_i40 : Litex.Representation M _Host_i40] (_value_i40 : Litex.Obj (M := M) _Host_i40) (h_33445 : Litex.In _value_i40 (Litex.RPos (M := M))), ∃ (_value_i41 : Litex.Obj (M := M) M.Value), ∃ (h_33451 : Litex.In _value_i41 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_33449 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))))), (by
            have h_33452 : (M.mem (Litex.denote _value_i41) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_33449 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i41 _litex_builder).mp h_33451)).choose
                  )
              )
            exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i41 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_33452) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.subInR _value_i41 (Litex.number (M := M) (0 : ℂ)) h_33452 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i41 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_33452) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.subInR _value_i41 (Litex.number (M := M) (0 : ℂ)) h_33452 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i40))
          ) from (by
            intro _Host_i40 _rep_i40 _value_i40 h_33445
            have h_33446 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i40 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_positive _value_i40 h_33445)
                  )
              )
            have h_33447 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i40 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i40 h_33446)
                  )
              )
            have h_33448 : ¬ Litex.Same _value_i40 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i40 h_33446) _litex_zero.symm)
                  )
              )
            exact ((h_157 (M := M)) (Litex.semanticObject (Litex.denote _value_i40) (Litex.isSet _value_i40)) h_33445)
          )) (show ∀ {_Host_i42 : Type _} [_rep_i42 : Litex.Representation M _Host_i42] (_value_i42 : Litex.Obj (M := M) _Host_i42) (h_34296 : Litex.In _value_i42 (Litex.RPos (M := M))), ∃ (_value_i43 : Litex.Obj (M := M) M.Value), ∃ (h_34300 : Litex.In _value_i43 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_34304 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i44 : Litex.Obj (M := M) M.Value) (h_34307 : Litex.In _value_i44 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_34304 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))))) => (by
            have h_34308 : (M.mem (Litex.denote _value_i44) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_34304 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i44 _litex_builder).mp h_34307)).choose
                  )
              )
            exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i44 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_34308) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.subInR _value_i44 (Litex.number (M := M) (0 : ℂ)) h_34308 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i44 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_34308) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.subInR _value_i44 (Litex.number (M := M) (0 : ℂ)) h_34308 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i43))
          ))) (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i45 : Litex.Obj (M := M) M.Value) (h_35261 : Litex.In _value_i45 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i45 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_35261) (Litex.numberInC (M := M) (0 : ℂ)));
          (Litex.abs _wd_2_0 (by
            let _atomic_wd_2_0 := _wd_2_0
            exact (Litex.subInR _value_i45 (Litex.number (M := M) (0 : ℂ)) h_35261 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i42));
          (by
            have _preimage_target : (by
            let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i45 : Litex.Obj (M := M) M.Value) (h_35517 : Litex.In _value_i45 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i45 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_35517) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_3_0 := _wd_2_0
              exact (Litex.subInR _value_i45 (Litex.number (M := M) (0 : ℂ)) h_35517 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i42))
            exact Litex.IsSet _atomic_wd_2_0) := (by
            let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i45 : Litex.Obj (M := M) M.Value) (h_35517 : Litex.In _value_i45 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i45 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_35517) (Litex.numberInC (M := M) (0 : ℂ)));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_3_0 := _wd_2_0
              exact (Litex.subInR _value_i45 (Litex.number (M := M) (0 : ℂ)) h_35517 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))))) _value_i42))
            exact (Litex.isSet _atomic_wd_2_0))
            let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i46 : Litex.Obj (M := M) M.Value) (h_35774 : Litex.In _value_i46 (Litex.R (M := M))) => ∃ (h_35772 : ¬ Litex.Same _value_i46 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i46 (h_150 (M := M)) h_35774 h_35772) _wd_1_1))
            exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_151 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))) from (by
            intro _Host_i42 _rep_i42 _value_i42 h_34296
            have h_34297 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i42 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_positive _value_i42 h_34296)
                  )
              )
            have h_34298 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i42 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i42 h_34297)
                  )
              )
            have h_34299 : ¬ Litex.Same _value_i42 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i42 h_34297) _litex_zero.symm)
                  )
              )
            exact ((h_5453 (M := M)) (Litex.semanticObject (Litex.denote _value_i42) (Litex.isSet _value_i42)) h_34296)
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
) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.finiteFunctionConvergentOfCandidate .both _function _point (Litex.number (M := M) (0 : ℂ)) (h_33417 (M := M))))

theorem h_36109 : (by
  let _equal_wd_1_0 := (_object_w232 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w232 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from ((Litex.finiteFunctionLimitEqCandidate _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (h_33417 (M := M))).trans (show @Eq M.Value _ _ from Eq.refl _))))
      )
  )

noncomputable def _object_w233 := (let _wd_1_0 := (_object_w232 (M := M));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (_object_w232 (M := M))
  exact (M.real_subset_complex _ (Litex.finiteFunctionLimitInR _atomic_wd_1_0))) (Litex.numberInC (M := M) (2 : ℂ))))

theorem h_36126 : (by
  let _equal_wd_1_0 := (_object_w233 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w233 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (by
          let _litex_zero_sum := _equal_wd_1_0
          have _litex_remaining : Litex.Same _litex_zero_sum.val.right (Litex.number (M := M) (2 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
          have _litex_zero : Litex.Same _litex_zero_sum.val.left (Litex.number (M := M) 0) := (h_36109 (M := M))
          have _litex_add_zero_result : Litex.Same _litex_zero_sum (Litex.number (M := M) (2 : ℂ)) := ((congrArg (fun zero_value => M.addValue zero_value (Litex.denote _litex_zero_sum.val.right)) _litex_zero).trans (Litex.zeroAdd _litex_zero_sum.val.right _litex_zero_sum.wd.2)).trans _litex_remaining
          exact _litex_add_zero_result
        )))
      )
  )

theorem h_36174 : (by
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
