import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_difference_x5f_bound_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_11 : Litex.In _value_i4 (Litex.R (M := M))) (h_1 : Litex.Lt _value_i1 _value_i2) (h_2 : Litex.Le _value_i3 _value_i4), (by
  let _atomic_wd_1_0 := (Litex.sub _value_i1 _value_i4 (M.real_subset_complex _ h_8) (M.real_subset_complex _ h_11))
  let _atomic_wd_1_1 := (Litex.sub _value_i2 _value_i3 (M.real_subset_complex _ h_9) (M.real_subset_complex _ h_10))
  exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8 _Host_i2 _rep_i2 _value_i2 h_9 _Host_i3 _rep_i3 _value_i3 h_10 _Host_i4 _rep_i4 _value_i4 h_11 h_1 h_2
          have h_338 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_339 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_340 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_341 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          let _object_w3 := (Litex.sub _value_i1 _value_i4 (M.real_subset_complex _ h_338) (M.real_subset_complex _ h_341))

          let _object_w4 := (Litex.sub _value_i2 _value_i4 (M.real_subset_complex _ h_339) (M.real_subset_complex _ h_341))

          have h_5 : (by
            let _atomic_wd_1_0 := _object_w3
            let _atomic_wd_1_1 := _object_w4
            exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    let _atomic_wd_1_1 := _object_w4
                    exact (by
                      let _litex_sub_left := _atomic_wd_1_0
                      let _litex_sub_right := _atomic_wd_1_1
                      exact Litex.subStructuralLtRight _litex_sub_left _litex_sub_right (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (Litex.subInR _value_i1 _value_i4 h_338 h_341)) h_1 (Litex.sameRefl _litex_sub_left.val.right)
                    ))
                )
            )
          let _object_w5 := (Litex.sub _value_i2 _value_i3 (M.real_subset_complex _ h_339) (M.real_subset_complex _ h_340))

          have h_6 : (by
            let _atomic_wd_1_0 := _object_w4
            let _atomic_wd_1_1 := _object_w5
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w4
                    let _atomic_wd_1_1 := _object_w5
                    exact (by
                      let _litex_sub_left := _atomic_wd_1_0
                      let _litex_sub_right := _atomic_wd_1_1
                      exact Litex.subStructuralLeLeft _litex_sub_left _litex_sub_right (by
                      let _atomic_wd_2_0 := _object_w4
                      exact (Litex.subInR _value_i2 _value_i4 h_339 h_341)) h_2 (Litex.sameRefl _litex_sub_left.val.left)
                    ))
                )
            )
          have h_7 : (by
            let _atomic_wd_1_0 := _object_w3
            let _atomic_wd_1_1 := _object_w5
            exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    let _atomic_wd_1_1 := _object_w5
                    exact (Litex.ltLeTrans _atomic_wd_1_0 _object_w4 _atomic_wd_1_1 h_5 h_6))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w3
            let _atomic_wd_1_1 := _object_w5
            exact h_7)
        )
      )
  )

theorem h_4331 : (by
  let _atomic_wd_1_0 := (Litex.sub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)))
  let _atomic_wd_1_1 := (Litex.sub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
  exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4332 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                )
            )
          have h_4333 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_4334 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
                )
            )
          have h_4335 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))
                )
            )
          have h_4336 : Litex.Lt (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_4332 h_4333).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) h_4332 = (1 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) h_4332).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) h_4333 = (2 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) h_4333).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))
                )
            )
          have h_4378 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_4332).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) h_4332 = (1 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) h_4332).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_4336)
                )
            )
          have h_4337 : Litex.Le (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) h_4334 h_4335).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) h_4334 = (3 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) h_4334).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) h_4335 = (4 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) h_4335).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))
                )
            )
          have h_4399 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_4334).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) h_4334 = (3 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) h_4334).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_4337)
                )
            )
          have h_4338 : Litex.Lt (Litex.sub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ))) (Litex.sub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_4 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_4332 (Litex.number (M := M) (2 : ℂ)) h_4333 (Litex.number (M := M) (3 : ℂ)) h_4334 (Litex.number (M := M) (4 : ℂ)) h_4335 h_4336 h_4337)
                )
            )
          exact (by
          let _atomic_wd_1_0 := (Litex.sub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)))
          let _atomic_wd_1_1 := (Litex.sub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
          exact h_4338)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_difference_x5f_bound_x2f_statement_x2e_lit
