import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_choice_x5f_from_x5f_universal_x2f_statement_x2e_lit

universe u v1 v5 v7 v11
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_7 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i2 _value_i2 (M.real_subset_complex _ h_7) (M.real_subset_complex _ h_7)) (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_6) (M.real_subset_complex _ h_6)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6
          have h_62 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_5 : ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_63 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_63) (M.real_subset_complex _ h_63)) (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_62) (M.real_subset_complex _ h_62)) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i3 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)
                    have h_123 : Litex.In _value_i3 (Litex.R (M := M)) := h_62
                    have h_124 : Litex.Same _value_i3 _value_i1 := rfl
                    have h_125 : (by
                      let _equal_wd_1_0 := (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ (Litex.inOfSame _value_i3 _value_i1 (Litex.R (M := M)) (Litex.R (M := M)) h_124 (show @Eq M.Value _ _ from Eq.refl _) h_123)) (M.real_subset_complex _ (Litex.inOfSame _value_i3 _value_i1 (Litex.R (M := M)) (Litex.R (M := M)) h_124 (show @Eq M.Value _ _ from Eq.refl _) h_123)))
                      let _equal_wd_1_1 := _equal_wd_1_0
                      exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ⟨_value_i3, h_123, h_125⟩
                )
            )
          exact h_5
        )
      )
  )

theorem h_302 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

variable {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_303 : Litex.In _value_i5 (Litex.R (M := M)))

noncomputable def _value_i6 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_303 : Litex.In _value_i5 (Litex.R (M := M))) : Litex.Obj (M := M) M.Value :=
  Classical.choose ((show ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_306 : Litex.In _value_i6 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306)) (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_303) (M.real_subset_complex _ h_303)) from (by
  have h_370 : Litex.In _value_i5 (Litex.R (M := M)) :=
    h_303
  rcases ((h_3 (M := M)) _value_i5 h_370) with ⟨_value_i6, h_306, h_304⟩
  have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
  have _exist_match_1 : Litex.Same (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306)) (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306)) := (Litex.sameRefl (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306)))
  have _exist_match_2 : Litex.Same (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_303) (M.real_subset_complex _ h_303)) (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_303) (M.real_subset_complex _ h_303)) := (congrArg₂ M.mulValue (Litex.sameRefl _value_i5) (Litex.sameRefl _value_i5))
  exact ⟨_value_i6, h_306, h_304⟩
)))

theorem h_375 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_303 : Litex.In _value_i5 (Litex.R (M := M))) : Litex.In (_value_i6 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_303) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((show ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_306 : Litex.In _value_i6 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306)) (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_303) (M.real_subset_complex _ h_303)) from (by
          have h_370 : Litex.In _value_i5 (Litex.R (M := M)) :=
            h_303
          rcases ((h_3 (M := M)) _value_i5 h_370) with ⟨_value_i6, h_306, h_304⟩
          have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
          have _exist_match_1 : Litex.Same (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306)) (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306)) := (Litex.sameRefl (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306)))
          have _exist_match_2 : Litex.Same (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_303) (M.real_subset_complex _ h_303)) (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_303) (M.real_subset_complex _ h_303)) := (congrArg₂ M.mulValue (Litex.sameRefl _value_i5) (Litex.sameRefl _value_i5))
          exact ⟨_value_i6, h_306, h_304⟩
        ))))))
      )
  )

theorem h_304 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_303 : Litex.In _value_i5 (Litex.R (M := M))) : Litex.Same ((fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_306 : Litex.In _value_i6 (Litex.R (M := M))) => (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306))) (_value_i6 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_303) (h_375 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_303)) ((fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_306 : Litex.In _value_i6 (Litex.R (M := M))) => (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_303) (M.real_subset_complex _ h_303))) (_value_i6 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_303) (h_375 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_303)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_306 : Litex.In _value_i6 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306)) (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_303) (M.real_subset_complex _ h_303)) from (by
          have h_370 : Litex.In _value_i5 (Litex.R (M := M)) :=
            h_303
          rcases ((h_3 (M := M)) _value_i5 h_370) with ⟨_value_i6, h_306, h_304⟩
          have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
          have _exist_match_1 : Litex.Same (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306)) (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306)) := (Litex.sameRefl (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306)))
          have _exist_match_2 : Litex.Same (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_303) (M.real_subset_complex _ h_303)) (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_303) (M.real_subset_complex _ h_303)) := (congrArg₂ M.mulValue (Litex.sameRefl _value_i5) (Litex.sameRefl _value_i5))
          exact ⟨_value_i6, h_306, h_304⟩
        ))))))
      )
  )

theorem h_376 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_303 : Litex.In _value_i5 (Litex.R (M := M))) : (by
  let _equal_wd_1_0 := ((fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_306 : Litex.In _value_i6 (Litex.R (M := M))) => (Litex.mul _value_i6 _value_i6 (M.real_subset_complex _ h_306) (M.real_subset_complex _ h_306))) (_value_i6 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_303) (h_375 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_303))
  let _equal_wd_1_1 := ((fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_306 : Litex.In _value_i6 (Litex.R (M := M))) => (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_303) (M.real_subset_complex _ h_303))) (_value_i6 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_303) (h_375 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_303))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_304 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_303)
      )
  )

theorem h_381 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_303 : Litex.In _value_i5 (Litex.R (M := M))) : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_385 : Litex.In _value_i7 (Litex.R (M := M))) (h_378 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ))), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_386 : Litex.In _value_i8 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i8 _value_i7 (M.real_subset_complex _ h_386) (M.real_subset_complex _ h_385)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_385 h_378
          have h_426 : Litex.In _value_i7 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_385
                )
            )
          have h_383 : ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_427 : Litex.In _value_i9 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i9 _value_i7 (M.real_subset_complex _ h_427) (M.real_subset_complex _ h_426)) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i9 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_426) h_378)) (Litex.isSet (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_426) h_378))
                    have h_544 : Litex.In _value_i9 (Litex.R (M := M)) := (by
                      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_426) h_378)
                      exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_426 (_atomic_wd_1_0).wd.2.2))
                    have h_545 : Litex.Same _value_i9 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_426) h_378) := rfl
                    let _object_w24 := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_426) h_378);
                    let _wd_1_1 := _value_i7;
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (M.real_subset_complex _ (Litex.inOfSame _value_i9 _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) h_545 (show @Eq M.Value _ _ from Eq.refl _) h_544))) (M.real_subset_complex _ h_426)))

                    have h_384 : (by
                      let _equal_wd_1_0 := _object_w24
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w24;
                            (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (by
                              let _quotient := (_equal_wd_1_0).val.left
                              let _product := _equal_wd_1_0
                              have _child : (by
                                let _equal_wd_2_0 := (_equal_wd_1_0).val.left
                                let _equal_wd_2_1 := _equal_wd_2_0
                                exact Litex.Same _equal_wd_2_1 _equal_wd_2_1) := (show @Eq M.Value _ _ from Eq.refl _)
                              have _conversion := Litex.sameDivIffSameMul _quotient.val.left _quotient.val.right _product.val.left _quotient.wd.1 _quotient.wd.2.1 _product.wd.1 _quotient.wd.2.2
                              exact ((_conversion.mp _child).symm))))
                          )
                      )
                    have h_671 : (by
                      let _equal_wd_1_0 := _object_w24
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) := h_384
                    exact ⟨_value_i9, h_544, h_671⟩
                )
            )
          exact h_383
        )
      )
  )

theorem h_757 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_303 : Litex.In _value_i5 (Litex.R (M := M))) : ∀ {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_761 : Litex.In _value_i11 (Litex.R (M := M))) (h_754 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))), ∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_762 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i12 _value_i11 (M.real_subset_complex _ h_762) (M.real_subset_complex _ h_761)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i11 _rep_i11 _value_i11 h_761 h_754
          have h_802 : Litex.In _value_i11 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_761
                )
            )
          rcases (show ∃ (_value_i13 : Litex.Obj (M := M) M.Value), ∃ (h_804 : Litex.In _value_i13 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i13 _value_i11 (M.real_subset_complex _ h_804) (M.real_subset_complex _ h_802)) (Litex.number (M := M) (1 : ℂ)) from (by
            have h_863 : Litex.In _value_i11 (Litex.R (M := M)) :=
              h_802
            have h_868 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
              h_754
            rcases ((h_381 (M := M) (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_303) _value_i11 h_863 h_868) with ⟨_value_i13, h_804, h_758⟩
            have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
            have _exist_match_1 : Litex.Same (Litex.mul _value_i13 _value_i11 (M.real_subset_complex _ h_804) (M.real_subset_complex _ h_802)) (Litex.mul _value_i13 _value_i11 (M.real_subset_complex _ h_804) (M.real_subset_complex _ h_802)) := (congrArg₂ M.mulValue (Litex.sameRefl _value_i13) (Litex.sameRefl _value_i11))
            have _exist_match_2 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))
            exact ⟨_value_i13, h_804, h_758⟩
          )) with ⟨_value_i13, h_873, h_758⟩
          have h_760 : ∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (h_874 : Litex.In _value_i14 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i14 _value_i11 (M.real_subset_complex _ h_874) (M.real_subset_complex _ h_802)) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i14 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _value_i13) (Litex.isSet _value_i13)
                    have h_927 : Litex.In _value_i14 (Litex.R (M := M)) := h_873
                    have h_928 : Litex.Same _value_i14 _value_i13 := rfl
                    have h_929 : (by
                      let _equal_wd_1_0 := ((fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_804 : Litex.In _value_i13 (Litex.R (M := M))) => (Litex.mul _value_i13 _value_i11 (M.real_subset_complex _ h_804) (M.real_subset_complex _ h_802))) _value_i13 h_873)
                      exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) := h_758
                    exact ⟨_value_i14, h_927, h_929⟩
                )
            )
          exact h_760
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_choice_x5f_from_x5f_universal_x2f_statement_x2e_lit
