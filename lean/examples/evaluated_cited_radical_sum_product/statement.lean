import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_cited_x5f_radical_x5f_sum_x5f_product_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_i1 := (Litex.number (M := M) (2 : ℂ))
theorem h_3 : Litex.In (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
      )
  )
theorem h_4 : Litex.Same (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))
      )
  )

theorem h_1293 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.sqrt (_object_i1 (M := M)) (h_3 (M := M)) (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) ((h_4 (M := M))).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M))) = (2 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))));
  let _wd_2_1 := (Litex.sqrt (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (M.real_subset_complex _ (by
      let _litex_sqrt := _atomic_wd_1_0
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    ))) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (M.real_subset_complex _ (by
      let _litex_sqrt := _atomic_wd_1_0
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )))));
  let _wd_1_1 := (let _wd_2_0 := (Litex.sqrt (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  let _wd_2_1 := (Litex.sqrt (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) = (7 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (M.real_subset_complex _ (by
      let _litex_sqrt := _atomic_wd_1_0
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    ))) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (M.real_subset_complex _ (by
      let _litex_sqrt := _atomic_wd_1_0
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )))));
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ (by
      let _litex_sqrt := (_atomic_wd_1_0).val.left
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )) (M.real_subset_complex _ (by
      let _litex_sqrt := (_atomic_wd_1_0).val.right
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ (by
      let _litex_sqrt := (_atomic_wd_1_0).val.left
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )) (M.real_subset_complex _ (by
      let _litex_sqrt := (_atomic_wd_1_0).val.right
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    ))))))
  let _equal_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.sqrt (Litex.number (M := M) (10 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (10 : ℂ) (10 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (10 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (10 : ℂ) (10 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (10 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (10 : ℂ) (10 : ℝ) (by norm_num)) = (10 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (10 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (10 : ℂ) (10 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (10 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  let _wd_3_1 := (Litex.sqrt (Litex.number (M := M) (14 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (14 : ℂ) (14 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (14 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (14 : ℂ) (14 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (14 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (14 : ℂ) (14 : ℝ) (by norm_num)) = (14 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (14 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (14 : ℂ) (14 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (14 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  (Litex.add _wd_3_0 _wd_3_1 (by
    let _atomic_wd_1_0 := _wd_3_0
    exact (M.real_subset_complex _ (by
      let _litex_sqrt := _atomic_wd_1_0
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    ))) (by
    let _atomic_wd_1_0 := _wd_3_1
    exact (M.real_subset_complex _ (by
      let _litex_sqrt := _atomic_wd_1_0
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )))));
  let _wd_2_1 := (Litex.sqrt (Litex.number (M := M) (15 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (15 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (15 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) = (15 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (15 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ (by
      let _litex_sqrt := (_atomic_wd_1_0).val.left
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )) (M.real_subset_complex _ (by
      let _litex_sqrt := (_atomic_wd_1_0).val.right
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )))) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (M.real_subset_complex _ (by
      let _litex_sqrt := _atomic_wd_1_0
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )))));
  let _wd_1_1 := (Litex.sqrt (Litex.number (M := M) (21 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (21 : ℂ) (21 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (21 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (21 : ℂ) (21 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (21 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (21 : ℂ) (21 : ℝ) (by norm_num)) = (21 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (21 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (21 : ℂ) (21 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (21 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.addInC ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right (M.real_subset_complex _ (by
      let _litex_sqrt := ((_atomic_wd_1_0).val.left).val.left
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )) (M.real_subset_complex _ (by
      let _litex_sqrt := ((_atomic_wd_1_0).val.left).val.right
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    ))) (M.real_subset_complex _ (by
      let _litex_sqrt := (_atomic_wd_1_0).val.right
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (by
      let _litex_sqrt := _atomic_wd_1_0
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    )))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.sqrt (_object_i1 (M := M)) (h_3 (M := M)) (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) ((h_4 (M := M))).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M))) = (2 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.inOfSame (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))));
        let _wd_2_1 := (Litex.sqrt (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        (Litex.add _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (M.real_subset_complex _ (by
            let _litex_sqrt := _atomic_wd_1_0
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          ))) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (M.real_subset_complex _ (by
            let _litex_sqrt := _atomic_wd_1_0
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )))));
        let _wd_1_1 := (let _wd_2_0 := (Litex.sqrt (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        let _wd_2_1 := (Litex.sqrt (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) = (7 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        (Litex.add _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (M.real_subset_complex _ (by
            let _litex_sqrt := _atomic_wd_1_0
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          ))) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (M.real_subset_complex _ (by
            let _litex_sqrt := _atomic_wd_1_0
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )))));
        (Litex.mul _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ (by
            let _litex_sqrt := (_atomic_wd_1_0).val.left
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )) (M.real_subset_complex _ (by
            let _litex_sqrt := (_atomic_wd_1_0).val.right
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ (by
            let _litex_sqrt := (_atomic_wd_1_0).val.left
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )) (M.real_subset_complex _ (by
            let _litex_sqrt := (_atomic_wd_1_0).val.right
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          ))))));
        let _equal_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.sqrt (Litex.number (M := M) (10 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (10 : ℂ) (10 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (10 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (10 : ℂ) (10 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (10 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (10 : ℂ) (10 : ℝ) (by norm_num)) = (10 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (10 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (10 : ℂ) (10 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (10 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        let _wd_3_1 := (Litex.sqrt (Litex.number (M := M) (14 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (14 : ℂ) (14 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (14 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (14 : ℂ) (14 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (14 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (14 : ℂ) (14 : ℝ) (by norm_num)) = (14 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (14 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (14 : ℂ) (14 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (14 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        (Litex.add _wd_3_0 _wd_3_1 (by
          let _atomic_wd_1_0 := _wd_3_0
          exact (M.real_subset_complex _ (by
            let _litex_sqrt := _atomic_wd_1_0
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          ))) (by
          let _atomic_wd_1_0 := _wd_3_1
          exact (M.real_subset_complex _ (by
            let _litex_sqrt := _atomic_wd_1_0
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )))));
        let _wd_2_1 := (Litex.sqrt (Litex.number (M := M) (15 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (15 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (15 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) = (15 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (15 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        (Litex.add _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ (by
            let _litex_sqrt := (_atomic_wd_1_0).val.left
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )) (M.real_subset_complex _ (by
            let _litex_sqrt := (_atomic_wd_1_0).val.right
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )))) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (M.real_subset_complex _ (by
            let _litex_sqrt := _atomic_wd_1_0
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )))));
        let _wd_1_1 := (Litex.sqrt (Litex.number (M := M) (21 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (21 : ℂ) (21 : ℝ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (21 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (21 : ℂ) (21 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (21 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (21 : ℂ) (21 : ℝ) (by norm_num)) = (21 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (21 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (21 : ℂ) (21 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (21 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
        (Litex.add _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.addInC ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right (M.real_subset_complex _ (by
            let _litex_sqrt := ((_atomic_wd_1_0).val.left).val.left
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )) (M.real_subset_complex _ (by
            let _litex_sqrt := ((_atomic_wd_1_0).val.left).val.right
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          ))) (M.real_subset_complex _ (by
            let _litex_sqrt := (_atomic_wd_1_0).val.right
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (M.real_subset_complex _ (by
            let _litex_sqrt := _atomic_wd_1_0
            exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
          )))));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((show Litex.denote _equal_wd_1_0 = (M.mulValue (M.addValue (Litex.sqrtValue (M := M) (Litex.denote (_object_i1 (M := M)))) (Litex.sqrtValue (M := M) (M.number (3 : ℂ)))) (M.addValue (Litex.sqrtValue (M := M) (M.number (5 : ℂ))) (Litex.sqrtValue (M := M) (M.number (7 : ℂ))))) from congrArg₂ M.mulValue (show Litex.denote (_equal_wd_1_0).val.left = (M.addValue (Litex.sqrtValue (M := M) (Litex.denote (_object_i1 (M := M)))) (Litex.sqrtValue (M := M) (M.number (3 : ℂ)))) from congrArg₂ M.addValue (show Litex.denote ((_equal_wd_1_0).val.left).val.left = (Litex.sqrtValue (M := M) (Litex.denote (_object_i1 (M := M)))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (show Litex.denote ((_equal_wd_1_0).val.left).val.right = (Litex.sqrtValue (M := M) (M.number (3 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))) (show Litex.denote (_equal_wd_1_0).val.right = (M.addValue (Litex.sqrtValue (M := M) (M.number (5 : ℂ))) (Litex.sqrtValue (M := M) (M.number (7 : ℂ)))) from congrArg₂ M.addValue (show Litex.denote ((_equal_wd_1_0).val.right).val.left = (Litex.sqrtValue (M := M) (M.number (5 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (5 : ℂ)) = (M.number (5 : ℂ)) from rfl)) (show Litex.denote ((_equal_wd_1_0).val.right).val.right = (Litex.sqrtValue (M := M) (M.number (7 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (7 : ℂ)) = (M.number (7 : ℂ)) from rfl))))).trans (((congrArg₂ M.mulValue (congrArg₂ M.addValue (congrArg (Litex.sqrtValue (M := M)) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (h_4 (M := M))) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl))) (Eq.refl (Litex.sqrtValue (M := M) (M.number (3 : ℂ))))) (Eq.refl (M.addValue (Litex.sqrtValue (M := M) (M.number (5 : ℂ))) (Litex.sqrtValue (M := M) (M.number (7 : ℂ))))))).trans ((((congrArg₂ M.mulValue ((congrArg₂ M.addValue ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (2 : ℝ)))) ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (3 : ℝ))))).trans (M.add_numbers ((Real.sqrt (2 : ℝ) : ℝ) : ℂ) ((Real.sqrt (3 : ℝ) : ℝ) : ℂ))) ((congrArg₂ M.addValue ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (5 : ℂ)) = M.number (5 : ℂ) from (congrArg M.number (show (5 : ℂ) = (5 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (5 : ℝ)))) ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (7 : ℂ) = (((7 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (7 : ℝ))))).trans (M.add_numbers ((Real.sqrt (5 : ℝ) : ℝ) : ℂ) ((Real.sqrt (7 : ℝ) : ℝ) : ℂ)))).trans (M.mul_numbers (((Real.sqrt (2 : ℝ) : ℝ) : ℂ) + ((Real.sqrt (3 : ℝ) : ℝ) : ℂ)) (((Real.sqrt (5 : ℝ) : ℝ) : ℂ) + ((Real.sqrt (7 : ℝ) : ℝ) : ℂ))))).trans ((congrArg M.number (by
          have _litex_pair_0 : ((Real.sqrt (2 : ℝ) : ℝ) : ℂ) * ((Real.sqrt (5 : ℝ) : ℝ) : ℂ) = ((Real.sqrt (10 : ℝ) : ℝ) : ℂ) := by
            have _litex_product : Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) = Real.sqrt (10 : ℝ) := by
              rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
              apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
            exact_mod_cast _litex_product
          have _litex_pair_1 : ((Real.sqrt (2 : ℝ) : ℝ) : ℂ) * ((Real.sqrt (7 : ℝ) : ℝ) : ℂ) = ((Real.sqrt (14 : ℝ) : ℝ) : ℂ) := by
            have _litex_product : Real.sqrt (2 : ℝ) * Real.sqrt (7 : ℝ) = Real.sqrt (14 : ℝ) := by
              rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
              apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (14 : ℝ) by norm_num)]
            exact_mod_cast _litex_product
          have _litex_pair_2 : ((Real.sqrt (3 : ℝ) : ℝ) : ℂ) * ((Real.sqrt (5 : ℝ) : ℝ) : ℂ) = ((Real.sqrt (15 : ℝ) : ℝ) : ℂ) := by
            have _litex_product : Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ) = Real.sqrt (15 : ℝ) := by
              rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
              apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num)]
            exact_mod_cast _litex_product
          have _litex_pair_3 : ((Real.sqrt (3 : ℝ) : ℝ) : ℂ) * ((Real.sqrt (7 : ℝ) : ℝ) : ℂ) = ((Real.sqrt (21 : ℝ) : ℝ) : ℂ) := by
            have _litex_product : Real.sqrt (3 : ℝ) * Real.sqrt (7 : ℝ) = Real.sqrt (21 : ℝ) := by
              rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
              apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
            exact_mod_cast _litex_product
          linear_combination (1 : ℂ) * _litex_pair_0 + (1 : ℂ) * _litex_pair_1 + (1 : ℂ) * _litex_pair_2 + (1 : ℂ) * _litex_pair_3 : ((((Real.sqrt (2 : ℝ) : ℝ) : ℂ) + ((Real.sqrt (3 : ℝ) : ℝ) : ℂ)) * (((Real.sqrt (5 : ℝ) : ℝ) : ℂ) + ((Real.sqrt (7 : ℝ) : ℝ) : ℂ))) = (((((Real.sqrt (10 : ℝ) : ℝ) : ℂ) + ((Real.sqrt (14 : ℝ) : ℝ) : ℂ)) + ((Real.sqrt (15 : ℝ) : ℝ) : ℂ)) + ((Real.sqrt (21 : ℝ) : ℝ) : ℂ)))).trans ((((congrArg₂ M.addValue ((congrArg₂ M.addValue ((congrArg₂ M.addValue ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (10 : ℂ)) = M.number (10 : ℂ) from (congrArg M.number (show (10 : ℂ) = (10 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (10 : ℂ) = (((10 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (10 : ℝ)))) ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (14 : ℂ)) = M.number (14 : ℂ) from (congrArg M.number (show (14 : ℂ) = (14 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (14 : ℂ) = (((14 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (14 : ℝ))))).trans (M.add_numbers ((Real.sqrt (10 : ℝ) : ℝ) : ℂ) ((Real.sqrt (14 : ℝ) : ℝ) : ℂ))) ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (15 : ℂ)) = M.number (15 : ℂ) from (congrArg M.number (show (15 : ℂ) = (15 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (15 : ℂ) = (((15 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (15 : ℝ))))).trans (M.add_numbers (((Real.sqrt (10 : ℝ) : ℝ) : ℂ) + ((Real.sqrt (14 : ℝ) : ℝ) : ℂ)) ((Real.sqrt (15 : ℝ) : ℝ) : ℂ))) ((congrArg (Litex.sqrtValue (M := M)) (show (M.number (21 : ℂ)) = M.number (21 : ℂ) from (congrArg M.number (show (21 : ℂ) = (21 : ℂ) from by norm_num)))).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) (by norm_num : (21 : ℂ) = (((21 : ℝ) : ℝ) : ℂ))).trans (Litex.sqrtValue_number (M := M) (21 : ℝ))))).trans (M.add_numbers ((((Real.sqrt (10 : ℝ) : ℝ) : ℂ) + ((Real.sqrt (14 : ℝ) : ℝ) : ℂ)) + ((Real.sqrt (15 : ℝ) : ℝ) : ℂ)) ((Real.sqrt (21 : ℝ) : ℝ) : ℂ)))).symm.trans ((show Litex.denote _equal_wd_1_1 = (M.addValue (M.addValue (M.addValue (Litex.sqrtValue (M := M) (M.number (10 : ℂ))) (Litex.sqrtValue (M := M) (M.number (14 : ℂ)))) (Litex.sqrtValue (M := M) (M.number (15 : ℂ)))) (Litex.sqrtValue (M := M) (M.number (21 : ℂ)))) from congrArg₂ M.addValue (show Litex.denote (_equal_wd_1_1).val.left = (M.addValue (M.addValue (Litex.sqrtValue (M := M) (M.number (10 : ℂ))) (Litex.sqrtValue (M := M) (M.number (14 : ℂ)))) (Litex.sqrtValue (M := M) (M.number (15 : ℂ)))) from congrArg₂ M.addValue (show Litex.denote ((_equal_wd_1_1).val.left).val.left = (M.addValue (Litex.sqrtValue (M := M) (M.number (10 : ℂ))) (Litex.sqrtValue (M := M) (M.number (14 : ℂ)))) from congrArg₂ M.addValue (show Litex.denote (((_equal_wd_1_1).val.left).val.left).val.left = (Litex.sqrtValue (M := M) (M.number (10 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (10 : ℂ)) = (M.number (10 : ℂ)) from rfl)) (show Litex.denote (((_equal_wd_1_1).val.left).val.left).val.right = (Litex.sqrtValue (M := M) (M.number (14 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (14 : ℂ)) = (M.number (14 : ℂ)) from rfl))) (show Litex.denote ((_equal_wd_1_1).val.left).val.right = (Litex.sqrtValue (M := M) (M.number (15 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (15 : ℂ)) = (M.number (15 : ℂ)) from rfl))) (show Litex.denote (_equal_wd_1_1).val.right = (Litex.sqrtValue (M := M) (M.number (21 : ℂ))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (Litex.number (M := M) (21 : ℂ)) = (M.number (21 : ℂ)) from rfl)))).symm)))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_cited_x5f_radical_x5f_sum_x5f_product_x2f_statement_x2e_lit
