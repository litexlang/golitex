import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_values_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_1 : (by
  let _atomic_wd_1_0 := (_object_w1 (M := M))
  exact Litex.In _atomic_wd_1_0 (Litex.QPos (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w1 (M := M))
          exact (Litex.inQPos_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num))) (Litex.NativeBridge.ltOfDenoteReal (Litex.number (M := M) 0) _atomic_wd_1_0 0 (0.5 : ℝ) rfl (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((0.5 : ℝ) : ℂ)))) (by norm_num))))
      )
  )

theorem h_5 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (_object_w1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inQPos_positive (_object_w1 (M := M)) (h_1 (M := M)))
      )
  )

theorem h_6 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (_object_w1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (Litex.number (M := M) 0) (_object_w1 (M := M)) (h_5 (M := M)))
      )
  )

theorem h_7 : ¬ Litex.Same (_object_w1 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (_object_w1 (M := M)) (h_5 (M := M))) _litex_zero.symm)
      )
  )

noncomputable def _object_w4 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_8 : (by
  let _atomic_wd_1_0 := (_object_w4 (M := M))
  exact Litex.In _atomic_wd_1_0 (Litex.QNeg (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w4 (M := M))
          exact (Litex.inQNeg_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((- (1 : ℂ)) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_1_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((- (1 : ℂ)) / (2 : ℂ)) ((-1 : ℚ) / (2 : ℚ)) (by norm_num))) (Litex.NativeBridge.ltOfDenoteReal _atomic_wd_1_0 (Litex.number (M := M) 0) (-0.5 : ℝ) 0 (((Litex.NativeBridge.denoteDiv (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_atomic_wd_1_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((- (1 : ℂ)) / (2 : ℂ)) = ((-0.5 : ℝ) : ℂ)))) rfl (by norm_num))))
      )
  )

theorem h_26 : Litex.Lt (_object_w4 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inQNeg_negative (_object_w4 (M := M)) (h_8 (M := M)))
      )
  )

theorem h_27 : Litex.Le (_object_w4 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (_object_w4 (M := M)) (Litex.number (M := M) 0) (h_26 (M := M)))
      )
  )

theorem h_28 : ¬ Litex.Same (_object_w4 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltNotSame (_object_w4 (M := M)) (Litex.number (M := M) 0) (h_26 (M := M)))
      )
  )

noncomputable def _object_w6 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))

theorem h_29 : (by
  let _atomic_wd_1_0 := (_object_w6 (M := M))
  exact Litex.In _atomic_wd_1_0 (Litex.ZNeg (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w6 (M := M))
          exact (Litex.inZNeg_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (3 : ℂ)) (-3 : ℤ) (by norm_num))) (Litex.NativeBridge.ltOfDenoteReal _atomic_wd_1_0 (Litex.number (M := M) 0) (-3 : ℝ) 0 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = ((-3 : ℝ) : ℂ)))) rfl (by norm_num))))
      )
  )

theorem h_39 : Litex.Lt (_object_w6 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inZNeg_negative (_object_w6 (M := M)) (h_29 (M := M)))
      )
  )

theorem h_40 : Litex.Le (_object_w6 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (_object_w6 (M := M)) (Litex.number (M := M) 0) (h_39 (M := M)))
      )
  )

theorem h_41 : ¬ Litex.Same (_object_w6 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltNotSame (_object_w6 (M := M)) (Litex.number (M := M) 0) (h_39 (M := M)))
      )
  )

noncomputable def _object_w8 := (Litex.neg (Litex.number (M := M) (0.25 : ℂ)) (Litex.numberInC (M := M) (0.25 : ℂ)))

theorem h_42 : (by
  let _atomic_wd_1_0 := (_object_w8 (M := M))
  exact Litex.In _atomic_wd_1_0 (Litex.RNeg (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w8 (M := M))
          exact (Litex.inRNeg_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (0.25 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (0.25 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (0.25 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (0.25 : ℂ)) ((-1 : ℝ) / (4 : ℝ)) (by norm_num))) (Litex.NativeBridge.ltOfDenoteReal _atomic_wd_1_0 (Litex.number (M := M) 0) (-0.25 : ℝ) 0 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (0.25 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (0.25 : ℂ)))).trans (congrArg M.number (by norm_num : (- (0.25 : ℂ)) = ((-0.25 : ℝ) : ℂ)))) rfl (by norm_num))))
      )
  )

theorem h_56 : Litex.Lt (_object_w8 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inRNeg_negative (_object_w8 (M := M)) (h_42 (M := M)))
      )
  )

theorem h_57 : Litex.Le (_object_w8 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (_object_w8 (M := M)) (Litex.number (M := M) 0) (h_56 (M := M)))
      )
  )

theorem h_58 : ¬ Litex.Same (_object_w8 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltNotSame (_object_w8 (M := M)) (Litex.number (M := M) 0) (h_56 (M := M)))
      )
  )

noncomputable def _object_w10 := (Litex.div (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_59 : (by
  let _atomic_wd_1_0 := (_object_w10 (M := M))
  exact Litex.In _atomic_wd_1_0 (Litex.QStar (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w10 (M := M))
          exact (Litex.inQStar_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((2 : ℂ) / (3 : ℂ)) ((2 : ℚ) / (3 : ℚ)) (by norm_num))) (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) 0) ((2 : ℂ) / (3 : ℂ)) 0 (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) rfl (by norm_num [Complex.ext_iff]))))
      )
  )

theorem h_95 : ¬ Litex.Same (_object_w10 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inQStar_nonzero (_object_w10 (M := M)) (h_59 (M := M)))
      )
  )

noncomputable def _object_w12 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))

theorem h_96 : (by
  let _atomic_wd_1_0 := (_object_w12 (M := M))
  exact Litex.In _atomic_wd_1_0 (Litex.ZStar (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w12 (M := M))
          exact (Litex.inZStar_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num))) (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) 0) (- (2 : ℂ)) 0 (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) rfl (by norm_num [Complex.ext_iff]))))
      )
  )

theorem h_118 : ¬ Litex.Same (_object_w12 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inZStar_nonzero (_object_w12 (M := M)) (h_96 (M := M)))
      )
  )

theorem h_119 : Litex.In (Litex.number (M := M) (0.25 : ℂ)) (Litex.RStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inRStar_intro (Litex.number (M := M) (0.25 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0.25 : ℂ) (0.25 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (0.25 : ℂ)) (Litex.number (M := M) 0) (0.25 : ℂ) 0 (Litex.NativeBridge.denoteNumber (M := M) (0.25 : ℂ)) rfl (by norm_num [Complex.ext_iff])))
      )
  )

theorem h_132 : ¬ Litex.Same (Litex.number (M := M) (0.25 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inRStar_nonzero (Litex.number (M := M) (0.25 : ℂ)) (h_119 (M := M)))
      )
  )

theorem h_133 : Litex.In (Litex.number (M := M) Complex.I) (Litex.CStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inCStar_intro (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) Complex.I) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) Complex.I) (Litex.number (M := M) 0) Complex.I 0 (Litex.NativeBridge.denoteNumber (M := M) Complex.I) rfl (by norm_num [Complex.ext_iff])))
      )
  )

theorem h_148 : ¬ Litex.Same (Litex.number (M := M) Complex.I) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inCStar_nonzero (Litex.number (M := M) Complex.I) (h_133 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_values_x2f_statement_x2e_lit
