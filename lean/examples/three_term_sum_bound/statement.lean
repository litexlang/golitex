import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_three_x5f_term_x5f_sum_x5f_bound_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6
variable {M : Litex.Semantics.{u}}

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_11 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_12 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 (Litex.R (M := M))) (h_1 : Litex.Le _value_i1 _value_i2) (h_2 : Litex.Le _value_i3 _value_i4) (h_3 : Litex.Lt _value_i5 _value_i6), (by
  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add _value_i1 _value_i3 (M.real_subset_complex _ h_8) (M.real_subset_complex _ h_10));
  let _wd_1_1 := _value_i5;
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_2_0 := _wd_1_0
    exact (Litex.addInC _value_i1 _value_i3 (M.real_subset_complex _ h_8) (M.real_subset_complex _ h_10))) (M.real_subset_complex _ h_12)))
  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add _value_i2 _value_i4 (M.real_subset_complex _ h_9) (M.real_subset_complex _ h_11));
  let _wd_1_1 := _value_i6;
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_2_0 := _wd_1_0
    exact (Litex.addInC _value_i2 _value_i4 (M.real_subset_complex _ h_9) (M.real_subset_complex _ h_11))) (M.real_subset_complex _ h_13)))
  exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8 _Host_i2 _rep_i2 _value_i2 h_9 _Host_i3 _rep_i3 _value_i3 h_10 _Host_i4 _rep_i4 _value_i4 h_11 _Host_i5 _rep_i5 _value_i5 h_12 _Host_i6 _rep_i6 _value_i6 h_13 h_1 h_2 h_3
          have h_1120 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_1121 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_1122 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_1123 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_1124 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_1125 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          let _object_w3 := (Litex.add _value_i1 _value_i3 (M.real_subset_complex _ h_1120) (M.real_subset_complex _ h_1122))

          let _object_w4 := (Litex.add _value_i2 _value_i4 (M.real_subset_complex _ h_1121) (M.real_subset_complex _ h_1123))

          have h_6 : (by
            let _atomic_wd_1_0 := _object_w3
            let _atomic_wd_1_1 := _object_w4
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    let _atomic_wd_1_1 := _object_w4
                    exact (Litex.addLeAdd _atomic_wd_1_0 _atomic_wd_1_1 h_1 h_2))
                )
            )
          let _object_w5 := (let _wd_1_0 := _object_w3;
          let _wd_1_1 := _value_i5;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w3
            exact (Litex.addInC _value_i1 _value_i3 (M.real_subset_complex _ h_1120) (M.real_subset_complex _ h_1122))) (M.real_subset_complex _ h_1124)))

          let _object_w6 := (let _wd_1_0 := _object_w4;
          let _wd_1_1 := _value_i6;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w4
            exact (Litex.addInC _value_i2 _value_i4 (M.real_subset_complex _ h_1121) (M.real_subset_complex _ h_1123))) (M.real_subset_complex _ h_1125)))

          have h_7 : (by
            let _atomic_wd_1_0 := _object_w5
            let _atomic_wd_1_1 := _object_w6
            exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    let _atomic_wd_1_1 := _object_w6
                    exact (Litex.addLtAddOfLeOfLt _atomic_wd_1_0 _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _object_w3
                      let _atomic_wd_2_1 := _object_w4
                      exact h_6) h_3))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w5
            let _atomic_wd_1_1 := _object_w6
            exact h_7)
        )
      )
  )

theorem h_9425 : (by
  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
  let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ))))
  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)));
  let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (6 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) + (4 : ℂ)) = (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ))))
  exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_9426 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                )
            )
          have h_9427 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_9428 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
                )
            )
          have h_9429 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))
                )
            )
          have h_9430 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))
                )
            )
          have h_9431 : Litex.In (Litex.number (M := M) (6 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num))
                )
            )
          have h_9432 : Litex.Le (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_9426 h_9427).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) h_9426 = (1 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) h_9426).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) h_9427 = (2 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) h_9427).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))
                )
            )
          have h_9478 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_9426).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) h_9426 = (1 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) h_9426).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_9432)
                )
            )
          have h_9433 : Litex.Le (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) h_9428 h_9429).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) h_9428 = (3 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) h_9428).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (4 : ℂ)) h_9429 = (4 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (4 : ℂ)) h_9429).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))
                )
            )
          have h_9537 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_9428).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) h_9428 = (3 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) h_9428).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_9433)
                )
            )
          have h_9434 : Litex.Lt (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (6 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (6 : ℂ)) h_9430 h_9431).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) h_9430 = (5 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) h_9430).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (6 : ℂ)) h_9431 = (6 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (6 : ℂ)) h_9431).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))
                )
            )
          have h_9647 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (6 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (6 : ℂ)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_9430).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) h_9430 = (5 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) h_9430).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_9434)
                )
            )
          have h_9435 : Litex.Lt (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ)))) (let _wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (6 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) + (4 : ℂ)) = (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ)))) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_5 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_9426 (Litex.number (M := M) (2 : ℂ)) h_9427 (Litex.number (M := M) (3 : ℂ)) h_9428 (Litex.number (M := M) (4 : ℂ)) h_9429 (Litex.number (M := M) (5 : ℂ)) h_9430 (Litex.number (M := M) (6 : ℂ)) h_9431 h_9432 h_9433 h_9434)
                )
            )
          have h_10187 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (6 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) + (4 : ℂ)) = (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ)))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
                  (Litex.add _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ)))) (let _wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
                  (Litex.add _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (6 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) + (4 : ℂ)) = (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ)))) (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
                    (Litex.add _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ))))
                    exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (3 : ℂ)) + (5 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (5 : ℂ)) (by
                        let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (3 : ℂ)) + (5 : ℂ)) (9 : ℝ) (by norm_num))))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (3 : ℂ)) + (5 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (5 : ℂ)) (by
                        let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (3 : ℂ)) + (5 : ℂ)) (9 : ℝ) (by norm_num)))) = (9 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (3 : ℂ)) + (5 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (5 : ℂ)) (by
                        let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (3 : ℂ)) + (5 : ℂ)) (9 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (5 : ℂ)) (by
                      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) h_9435)
                )
            )
          exact (by
          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ))))
          let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (6 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) + (4 : ℂ)) = (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ))))
          exact h_9435)
        )
      )
  )

theorem h_10221 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (6 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) + (4 : ℂ)) = (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
        let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
        (Litex.add _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ)))) (let _wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)));
        let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
        (Litex.add _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (6 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) + (4 : ℂ)) = (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ)))) (Litex.numberInC (M := M) (6 : ℂ)))) (by
          let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ))))
          exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (3 : ℂ)) + (5 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (5 : ℂ)) (by
              let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (3 : ℂ)) + (5 : ℂ)) (9 : ℝ) (by norm_num))))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (3 : ℂ)) + (5 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (5 : ℂ)) (by
              let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (3 : ℂ)) + (5 : ℂ)) (9 : ℝ) (by norm_num)))) = (9 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (((1 : ℂ) + (3 : ℂ)) + (5 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (5 : ℂ)) (by
              let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) + (3 : ℂ)) + (5 : ℂ)) (9 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (5 : ℂ)) (by
            let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (4 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (3 : ℂ)) = (4 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (h_9425 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_three_x5f_term_x5f_sum_x5f_bound_x2f_statement_x2e_lit
