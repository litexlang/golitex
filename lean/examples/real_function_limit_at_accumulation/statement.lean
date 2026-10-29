import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_function_x5f_limit_x5f_at_x5f_accumulation_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_7 : Litex.In _value_i2 (Litex.RPos (M := M))), ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i3 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i3 _value_i1 (M.real_subset_complex _ h_11) (M.real_subset_complex _ h_6));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i3 _value_i1 h_11 h_6))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i3 _value_i1 (M.real_subset_complex _ h_11) (M.real_subset_complex _ h_6));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i3 _value_i1 h_11 h_6)))) _value_i2)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_7
          have h_8 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i2 h_7)
                )
            )
          have h_9 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_8)
                )
            )
          have h_10 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_8) _litex_zero.symm)
                )
            )
          have h_624 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_625 : Litex.In _value_i2 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_626 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i2 h_625)
                )
            )
          have h_627 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_626)
                )
            )
          have h_628 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_626) _litex_zero.symm)
                )
            )
          have h_634 : ∀ (_value_i5 : Litex.Obj (M := M) M.Value) (h_1553 : Litex.In _value_i5 (Litex.RPos (M := M))), ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_1557 : Litex.In _value_i6 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i6 _value_i1 (M.real_subset_complex _ h_1557) (M.real_subset_complex _ h_624));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i6 _value_i1 h_1557 h_624))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i6 _value_i1 (M.real_subset_complex _ h_1557) (M.real_subset_complex _ h_624));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i6 _value_i1 h_1557 h_624)))) _value_i5)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_629 : Litex.In _value_i1 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_624
                          )
                      )
                    exact (show ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_639 : Litex.In _value_i5 (Litex.RPos (M := M))), ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_643 : Litex.In _value_i6 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i6 _value_i1 (M.real_subset_complex _ h_643) (M.real_subset_complex _ h_629));
                  (Litex.abs _wd_1_0 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.subInR _value_i6 _value_i1 h_643 h_629))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i6 _value_i1 (M.real_subset_complex _ h_643) (M.real_subset_complex _ h_629));
                  (Litex.abs _wd_1_0 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.subInR _value_i6 _value_i1 h_643 h_629)))) _value_i5)) from (by
                    intro _Host _rep _radius _radius_member
                    obtain ⟨_input, _input_member, _positive, _near⟩ := Litex.realFiniteLimitAccumulation .both _value_i1 h_629 _radius _radius_member
                    exact ⟨_input, _input_member, _positive, _near⟩
                  ))
                  )
                )
            )
          exact (by
            have h_2943 : Litex.In _value_i2 (Litex.RPos (M := M)) :=
              h_625
            rcases (h_634 (Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)) h_2943) with ⟨_value_i3, h_2315, h_3⟩
            have h_1 :=
              (And.left h_3)
            have h_2 :=
              (And.right h_3)
            have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
            have _exist_match_1 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (0 : ℂ)))
            have _exist_match_2 : Litex.Same (let _wd_1_0 := (Litex.sub _value_i3 _value_i1 (M.real_subset_complex _ h_2315) (M.real_subset_complex _ h_624));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i3 _value_i1 h_2315 h_624)))) (let _wd_1_0 := (Litex.sub _value_i3 _value_i1 (M.real_subset_complex _ h_2315) (M.real_subset_complex _ h_624));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i3 _value_i1 h_2315 h_624)))) := (Litex.sameRefl (let _wd_1_0 := (Litex.sub _value_i3 _value_i1 (M.real_subset_complex _ h_2315) (M.real_subset_complex _ h_624));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i3 _value_i1 h_2315 h_624)))))
            have _exist_match_3 : Litex.Same (let _wd_1_0 := (Litex.sub _value_i3 _value_i1 (M.real_subset_complex _ h_2315) (M.real_subset_complex _ h_624));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i3 _value_i1 h_2315 h_624)))) (let _wd_1_0 := (Litex.sub _value_i3 _value_i1 (M.real_subset_complex _ h_2315) (M.real_subset_complex _ h_624));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i3 _value_i1 h_2315 h_624)))) := (Litex.sameRefl (let _wd_1_0 := (Litex.sub _value_i3 _value_i1 (M.real_subset_complex _ h_2315) (M.real_subset_complex _ h_624));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i3 _value_i1 h_2315 h_624)))))
            have _exist_match_4 : Litex.Same _value_i2 _value_i2 := (Litex.sameRefl _value_i2)
            exact ⟨_value_i3, h_2315, h_3⟩
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_function_x5f_limit_x5f_at_x5f_accumulation_x2f_statement_x2e_lit
