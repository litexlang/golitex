import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_ray_x5f_endpoints_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w2 := (Litex.realRay true true (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))

theorem h_1 : (by
  let _atomic_wd_1_1 := (_object_w2 (M := M))
  exact Litex.In (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w2 (M := M))
          exact ((Litex.inRealRay_iff _atomic_wd_1_1 (Litex.number (M := M) (0 : ℂ))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))⟩))
      )
  )

theorem h_7 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        ((Litex.inRealRay_iff (_object_w2 (M := M)) (Litex.number (M := M) (0 : ℂ))).mp (h_1 (M := M))).1
      )
  )

theorem h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        ((Litex.inRealRay_iff (_object_w2 (M := M)) (Litex.number (M := M) (0 : ℂ))).mp (h_1 (M := M))).2
      )
  )

noncomputable def _object_w5 := (Litex.realRay true false (Litex.number (M := M) (0 : ℂ)) (h_7 (M := M)))

theorem h_9 : (by
  let _atomic_wd_1_1 := (_object_w5 (M := M))
  exact Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w5 (M := M))
          exact ((Litex.inRealRay_iff _atomic_wd_1_1 (Litex.number (M := M) (1 : ℂ))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_7 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (h_7 (M := M)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (h_7 (M := M))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))⟩))
      )
  )

theorem h_47 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        ((Litex.inRealRay_iff (_object_w5 (M := M)) (Litex.number (M := M) (1 : ℂ))).mp (h_9 (M := M))).1
      )
  )

theorem h_48 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        ((Litex.inRealRay_iff (_object_w5 (M := M)) (Litex.number (M := M) (1 : ℂ))).mp (h_9 (M := M))).2
      )
  )

noncomputable def _object_w6 := (Litex.realRay false true (Litex.number (M := M) (0 : ℂ)) (h_7 (M := M)))

theorem h_49 : (by
  let _atomic_wd_1_1 := (_object_w6 (M := M))
  exact Litex.In (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w6 (M := M))
          exact ((Litex.inRealRay_iff _atomic_wd_1_1 (Litex.number (M := M) (0 : ℂ))).mpr ⟨(h_7 (M := M)), (h_8 (M := M))⟩))
      )
  )

theorem h_97 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        ((Litex.inRealRay_iff (_object_w6 (M := M)) (Litex.number (M := M) (0 : ℂ))).mp (h_49 (M := M))).1
      )
  )

theorem h_98 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        ((Litex.inRealRay_iff (_object_w6 (M := M)) (Litex.number (M := M) (0 : ℂ))).mp (h_49 (M := M))).2
      )
  )

noncomputable def _object_w7 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))

noncomputable def _object_w8 := (Litex.realRay false false (Litex.number (M := M) (0 : ℂ)) (h_7 (M := M)))

theorem h_99 : (by
  let _atomic_wd_1_0 := (_object_w7 (M := M))
  let _atomic_wd_1_1 := (_object_w8 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w7 (M := M))
          let _atomic_wd_1_1 := (_object_w8 (M := M))
          exact ((Litex.inRealRay_iff _atomic_wd_1_1 _atomic_wd_1_0).mpr ⟨(by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))), (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact ((Litex.NativeBridge.lt_iff_asReal _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (by
              let _atomic_wd_3_0 := _atomic_wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) (h_7 (M := M))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_2_0 (by
              let _atomic_wd_3_0 := _atomic_wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) = (-1 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_0 (by
              let _atomic_wd_3_0 := _atomic_wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (h_7 (M := M)) = (0 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (h_7 (M := M))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))⟩))
      )
  )

theorem h_239 : Litex.In (_object_w7 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        ((Litex.inRealRay_iff (_object_w8 (M := M)) (_object_w7 (M := M))).mp (h_99 (M := M))).1
      )
  )

theorem h_240 : Litex.Lt (_object_w7 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        ((Litex.inRealRay_iff (_object_w8 (M := M)) (_object_w7 (M := M))).mp (h_99 (M := M))).2
      )
  )

theorem h_241 : (by
  let _atomic_wd_1_1 := (_object_w5 (M := M))
  exact ¬ Litex.In (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w5 (M := M))
          exact (Litex.notInRealRayEndpoint _atomic_wd_1_1 (Litex.number (M := M) (0 : ℂ)) (show @Eq M.Value _ _ from Eq.refl _)))
      )
  )

theorem h_244 : (by
  let _atomic_wd_1_1 := (_object_w8 (M := M))
  exact ¬ Litex.In (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w8 (M := M))
          exact (Litex.notInRealRayEndpoint _atomic_wd_1_1 (Litex.number (M := M) (0 : ℂ)) (show @Eq M.Value _ _ from Eq.refl _)))
      )
  )

theorem h_255 : (by
  let _atomic_wd_1_0 := (_object_w7 (M := M))
  let _atomic_wd_1_1 := (_object_w2 (M := M))
  exact ¬ Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w7 (M := M))
          let _atomic_wd_1_1 := (_object_w2 (M := M))
          exact (Litex.notInRealRayOpposite _atomic_wd_1_1 _atomic_wd_1_0 (by
            let _atomic_wd_2_0 := (_object_w7 (M := M))
            exact (h_240 (M := M)))))
      )
  )

theorem h_271 : (by
  let _atomic_wd_1_1 := (_object_w6 (M := M))
  exact ¬ Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w6 (M := M))
          exact (Litex.notInRealRayOpposite _atomic_wd_1_1 (Litex.number (M := M) (1 : ℂ)) (h_48 (M := M))))
      )
  )

theorem h_289 : (by
  let _atomic_wd_1_0 := (_object_w2 (M := M))
  exact Litex.Subset _atomic_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w2 (M := M))
          exact (Litex.realRaySubsetR _atomic_wd_1_0))
      )
  )

theorem h_293 : (by
  let _atomic_wd_1_0 := (_object_w8 (M := M))
  exact Litex.Subset _atomic_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w8 (M := M))
          exact (Litex.realRaySubsetR _atomic_wd_1_0))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_ray_x5f_endpoints_x2f_statement_x2e_lit
