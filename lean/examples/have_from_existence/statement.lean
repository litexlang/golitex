import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_have_x5f_from_x5f_existence_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_3 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i1 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.isSet (Litex.number (M := M) (2 : ℂ)))
          have h_5 : Litex.In _value_i1 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          have h_6 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) := rfl
          have h_7 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ⟨_value_i1, h_5, h_7⟩
      )
  )

noncomputable def _value_i2 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)) from ⟨Litex.semanticObject (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.isSet (Litex.number (M := M) (2 : ℂ))), (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (by rfl)⟩))

theorem h_13 : Litex.In (_value_i2 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)) from ⟨Litex.semanticObject (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.isSet (Litex.number (M := M) (2 : ℂ))), (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (by rfl)⟩)))))
      )
  )

theorem h_9 : Litex.Same (_value_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)) from ⟨Litex.semanticObject (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.isSet (Litex.number (M := M) (2 : ℂ))), (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (by rfl)⟩)))))
      )
  )

noncomputable def _object_w9 := (Litex.add (_value_i2 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_13 (M := M))) (Litex.numberInC (M := M) (1 : ℂ)))

theorem h_14 : (by
  let _equal_wd_1_0 := (_object_w9 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (((congrArg₂ M.addValue (h_9 (M := M)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))))).trans (((let _equal_wd_2_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
        (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((2 : ℂ) + (1 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))).trans ((Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))).symm))
      )
  )

theorem h_78 : ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_83 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
  (by
    litex_complete =>
      exact (
        (by
          rcases (show ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_95 : Litex.In _value_i4 (Litex.R (M := M))), Litex.Same _value_i4 (Litex.number (M := M) (2 : ℂ)) from ⟨Litex.semanticObject (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.isSet (Litex.number (M := M) (2 : ℂ))), (Litex.inOfSame (_value_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_9 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_13 (M := M))), (by rfl)⟩) with ⟨_value_i4, h_101, h_79⟩
          have h_81 : ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_102 : Litex.In _value_i5 (Litex.R (M := M))), Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i5 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _value_i4) (Litex.isSet _value_i4)
                    have h_120 : Litex.In _value_i5 (Litex.R (M := M)) := h_101
                    have h_121 : Litex.Same _value_i5 _value_i4 := rfl
                    have h_82 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) _value_i4 (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (h_79).symm ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.inOfSame _value_i5 (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) ((h_121).trans h_79) (show @Eq M.Value _ _ from Eq.refl _) h_120)).mpr (by
                              have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.inOfSame _value_i5 (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) ((h_121).trans h_79) (show @Eq M.Value _ _ from Eq.refl _) h_120) = (2 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.inOfSame _value_i5 (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) ((h_121).trans h_79) (show @Eq M.Value _ _ from Eq.refl _) h_120)).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                                apply Complex.ofReal_injective
                                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num))))
                          )
                      )
                    have h_206 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 := h_82
                    exact ⟨_value_i5, h_120, h_206⟩
                )
            )
          exact (by
            let _real_base := (Litex.number (M := M) (0 : ℂ))
            have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
            obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealAbove _real_base _real_base_member
            exact ⟨_real_witness, _real_member, _real_order⟩)
        )
      )
  )

theorem h_242 : ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_244 : Litex.In _value_i7 (Litex.R (M := M))), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_245 : Litex.In _value_i8 (Litex.R (M := M))), ∃ (h_240 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i7 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_245) h_240) :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i7 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.isSet (Litex.number (M := M) (1 : ℂ)))
          have h_281 : Litex.In _value_i7 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
          let _value_i8 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.isSet (Litex.number (M := M) (1 : ℂ)))
          have h_282 : Litex.In _value_i8 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
          have h_283 : Litex.Same _value_i7 (Litex.number (M := M) (1 : ℂ)) := rfl
          have h_284 : Litex.Same _value_i8 (Litex.number (M := M) (1 : ℂ)) := rfl
          let _object_w19 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

          have h_243 : (by
            let _equal_wd_1_0 := _object_w19
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w19;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) ((1 : ℂ) / (1 : ℂ)) (1 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
                )
            )
          have h_309 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
          have h_310 : (by
            let _equal_wd_1_1 := _object_w19
            exact Litex.Same (Litex.number (M := M) (1 : ℂ)) _equal_wd_1_1) := (h_243).symm
          exact ⟨_value_i7, h_281, _value_i8, h_282, h_309, h_310⟩
      )
  )

noncomputable def _value_i9 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((show ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_315 : Litex.In _value_i9 (Litex.R (M := M))), ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_316 : Litex.In _value_i10 (Litex.R (M := M))), ∃ (h_312 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i9 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_316) h_312) from (h_242 (M := M))))

theorem h_346 : Litex.In (_value_i9 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((show ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_315 : Litex.In _value_i9 (Litex.R (M := M))), ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_316 : Litex.In _value_i10 (Litex.R (M := M))), ∃ (h_312 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i9 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_316) h_312) from (h_242 (M := M)))))))
      )
  )

noncomputable def _value_i10 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_315 : Litex.In _value_i9 (Litex.R (M := M))), ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_316 : Litex.In _value_i10 (Litex.R (M := M))), ∃ (h_312 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i9 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_316) h_312) from (h_242 (M := M))))))))

theorem h_347 : Litex.In (_value_i10 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_315 : Litex.In _value_i9 (Litex.R (M := M))), ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_316 : Litex.In _value_i10 (Litex.R (M := M))), ∃ (h_312 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i9 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_316) h_312) from (h_242 (M := M)))))))))))
      )
  )

theorem h_312 : ¬ Litex.Same (_value_i10 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_315 : Litex.In _value_i9 (Litex.R (M := M))), ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_316 : Litex.In _value_i10 (Litex.R (M := M))), ∃ (h_312 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i9 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_316) h_312) from (h_242 (M := M)))))))))))))
      )
  )

theorem h_313 : Litex.Same (_value_i9 (M := M)) ((fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_315 : Litex.In _value_i9 (Litex.R (M := M))) (_value_i10 : Litex.Obj (M := M) M.Value) (h_316 : Litex.In _value_i10 (Litex.R (M := M))) (h_312 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ))) => (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_316) h_312)) (_value_i9 (M := M)) (h_346 (M := M)) (_value_i10 (M := M)) (h_347 (M := M)) (h_312 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_315 : Litex.In _value_i9 (Litex.R (M := M))), ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_316 : Litex.In _value_i10 (Litex.R (M := M))), ∃ (h_312 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i9 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_316) h_312) from (h_242 (M := M)))))))))))))
      )
  )

theorem h_348 : (by
  let _equal_wd_1_1 := ((fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_315 : Litex.In _value_i9 (Litex.R (M := M))) (_value_i10 : Litex.Obj (M := M) M.Value) (h_316 : Litex.In _value_i10 (Litex.R (M := M))) (h_312 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ))) => (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_316) h_312)) (_value_i9 (M := M)) (h_346 (M := M)) (_value_i10 (M := M)) (h_347 (M := M)) (h_312 (M := M)))
  exact Litex.Same (_value_i9 (M := M)) _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_313 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_have_x5f_from_x5f_existence_x2f_statement_x2e_lit
