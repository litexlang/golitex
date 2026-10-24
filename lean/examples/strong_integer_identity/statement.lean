import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_strong_x5f_integer_x5f_identity_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_230 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.Z (M := M))) (h_5 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1), Litex.Same _value_i1 _value_i1 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 h_5
          have h_20 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i1 h_4 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_5)
                )
            )
          exact Litex.integerStrongInductionFromZero (fun (_raw_i1 : M.Value) => (_raw_i1 = _raw_i1)) (by
            let _raw_i1 : M.Value := M.number 0
            have h_33 : M.mem _raw_i1 (M.standard .integer) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num))
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_33)
            have h_33 : Litex.In _value_i1 (Litex.Z (M := M)) := h_33
            have h_34 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by rfl)
                  )
              )
            have h_2 : Litex.Same _value_i1 _value_i1 :=
              (by
                litex_checked_step =>
                  exact (
                    (show @Eq M.Value _ _ from Eq.refl _)
                  )
              )
            show (fun (_raw_i1 : M.Value) => (_raw_i1 = _raw_i1)) (M.number 0)
            exact (show @Eq M.Value _ _ from Eq.refl _)
          ) (by
            intro _raw_i1 _induction_integer _induction_nonnegative _induction_hypothesis
            have h_38 : M.mem _raw_i1 (M.standard .integer) := _induction_integer
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_38)
            have h_38 : Litex.In _value_i1 (Litex.Z (M := M)) := h_38
            have h_39 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
              (by
                litex_checked_step =>
                  exact (
                    _induction_nonnegative
                  )
              )
            have h_54 : Litex.In _value_i1 (Litex.N (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i1 h_38 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_39)
                  )
              )
            have h_68 : ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_71 : Litex.In _value_i2 (Litex.Z (M := M))) (h_69 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2) (h_70 : Litex.Le _value_i2 _value_i1), Litex.Same _value_i2 _value_i2 :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      intro _Host_i2 _rep_i2 _value_i2 h_71 h_69 h_70
                      have h_99 : Litex.In _value_i2 (Litex.N (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i2 h_71 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_69)
                            )
                        )
                      exact (_induction_hypothesis (Litex.denote _value_i2) h_71 h_69 h_70)
                    )
                  )
              )
            have h_2 : Litex.Same _value_i1 _value_i1 :=
              (by
                litex_checked_step =>
                  exact (
                    (show @Eq M.Value _ _ from Eq.refl _)
                  )
              )
            show (fun (_raw_i1 : M.Value) => (_raw_i1 = _raw_i1)) (M.addValue _raw_i1 (M.number 1))
            exact (show @Eq M.Value _ _ from Eq.refl _)
          ) _value_i1 h_4 h_5
        )
      )
  )

theorem h_601 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_268 : Litex.In _value_i3 (Litex.Z (M := M))) (h_269 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3), Litex.Same _value_i3 _value_i3 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_268 h_269
          have h_284 : Litex.In _value_i3 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i3 h_268 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_269)
                )
            )
          exact Litex.integerStrongInductionFromZero (fun (_raw_i3 : M.Value) => (_raw_i3 = _raw_i3)) (by
            let _raw_i3 : M.Value := M.number 0
            have h_297 : M.mem _raw_i3 (M.standard .integer) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num))
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_297)
            have h_297 : Litex.In _value_i3 (Litex.Z (M := M)) := h_297
            have h_298 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by rfl)
                  )
              )
            have h_261 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (show @Eq M.Value _ _ from Eq.refl _)
                  )
              )
            show (fun (_raw_i3 : M.Value) => (_raw_i3 = _raw_i3)) (M.number 0)
            exact (show @Eq M.Value _ _ from Eq.refl _)
          ) (by
            intro _raw_i3 _induction_integer _induction_nonnegative _induction_hypothesis
            have h_302 : M.mem _raw_i3 (M.standard .integer) := _induction_integer
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_302)
            have h_302 : Litex.In _value_i3 (Litex.Z (M := M)) := h_302
            have h_303 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
              (by
                litex_checked_step =>
                  exact (
                    _induction_nonnegative
                  )
              )
            have h_318 : Litex.In _value_i3 (Litex.N (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i3 h_302 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_303)
                  )
              )
            have h_332 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_335 : Litex.In _value_i5 (Litex.Z (M := M))) (h_333 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5) (h_334 : Litex.Le _value_i5 _value_i3), Litex.Same _value_i5 _value_i5 :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      intro _Host_i5 _rep_i5 _value_i5 h_335 h_333 h_334
                      have h_363 : Litex.In _value_i5 (Litex.N (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i5 h_335 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_333)
                            )
                        )
                      exact (_induction_hypothesis (Litex.denote _value_i5) h_335 h_333 h_334)
                    )
                  )
              )
            have h_265 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_442 : Litex.In _value_i4 (Litex.Z (M := M))) (h_262 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4) (h_263 : Litex.Le _value_i4 _value_i3), Litex.Same _value_i4 _value_i4 :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      intro _Host_i4 _rep_i4 _value_i4 h_442 h_262 h_263
                      have h_470 : Litex.In _value_i4 (Litex.N (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (0 : ℂ)) _value_i4 h_442 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
                                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                  apply Complex.ofReal_injective
                                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_262)
                            )
                        )
                      exact (h_332 _value_i4 h_442 h_262 h_263)
                    )
                  )
              )
            let _object_w20 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i3 h_302) (Litex.numberInC (M := M) (1 : ℂ)))

            have h_266 : (by
              let _equal_wd_1_0 := _object_w20
              let _equal_wd_1_1 := _equal_wd_1_0
              exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show @Eq M.Value _ _ from Eq.refl _)
                  )
              )
            show (fun (_raw_i3 : M.Value) => (_raw_i3 = _raw_i3)) (M.addValue _raw_i3 (M.number 1))
            exact (show @Eq M.Value _ _ from Eq.refl _)
          ) _value_i3 h_268 h_269
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_strong_x5f_integer_x5f_identity_x2f_statement_x2e_lit
