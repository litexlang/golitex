import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_numeric_x5f_nonmembership_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))

theorem h_1 : (by
  let _atomic_wd_1_0 := (_object_w1 (M := M))
  exact ¬ Litex.In _atomic_wd_1_0 (Litex.N (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w1 (M := M))
          exact (Litex.notInOfSame _atomic_wd_1_0 (Litex.number (M := M) (((-1 : ℚ) : ℚ) : ℂ)) (Litex.N (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (((-1 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.numberNotInNOfNegative (M := M) (-1 : ℚ) (by norm_num)) _member)))
      )
  )

theorem h_3 : ¬ Litex.In (Litex.number (M := M) (1.5 : ℂ)) (Litex.N (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.notInOfSame (Litex.number (M := M) (1.5 : ℂ)) (Litex.number (M := M) (((1.5 : ℚ) : ℚ) : ℂ)) (Litex.N (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (1.5 : ℂ))).trans (congrArg M.number (by norm_num : (1.5 : ℂ) = (((1.5 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.numberNotInZOfDenominator (M := M) (1.5 : ℚ) (by norm_num)) (Litex.naturalToInteger (Litex.number (M := M) (((1.5 : ℚ) : ℚ) : ℂ)) _member)))
      )
  )

noncomputable def _object_w4 := (Litex.neg (Litex.number (M := M) (1.5 : ℂ)) (Litex.numberInC (M := M) (1.5 : ℂ)))

theorem h_6 : (by
  let _atomic_wd_1_0 := (_object_w4 (M := M))
  exact ¬ Litex.In _atomic_wd_1_0 (Litex.NPos (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w4 (M := M))
          exact (Litex.notInOfSame _atomic_wd_1_0 (Litex.number (M := M) (((-1.5 : ℚ) : ℚ) : ℂ)) (Litex.NPos (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1.5 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1.5 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1.5 : ℂ)) = (((-1.5 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.numberNotInZOfDenominator (M := M) (-1.5 : ℚ) (by norm_num)) (Litex.naturalToInteger (Litex.number (M := M) (((-1.5 : ℚ) : ℚ) : ℂ)) (Litex.inNPos_natural (Litex.number (M := M) (((-1.5 : ℚ) : ℚ) : ℂ)) _member)))))
      )
  )

theorem h_12 : ¬ Litex.In (Litex.number (M := M) (1.5 : ℂ)) (Litex.Z (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.notInOfSame (Litex.number (M := M) (1.5 : ℂ)) (Litex.number (M := M) (((1.5 : ℚ) : ℚ) : ℂ)) (Litex.Z (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (1.5 : ℂ))).trans (congrArg M.number (by norm_num : (1.5 : ℂ) = (((1.5 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.numberNotInZOfDenominator (M := M) (1.5 : ℚ) (by norm_num)) _member))
      )
  )

theorem h_21 : ¬ Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.NPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.notInOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) (Litex.NPos (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (((0 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.numberNotPositive (M := M) (0 : ℚ) (by norm_num)) (Litex.inNPos_positive (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) _member)))
      )
  )

theorem h_30 : ¬ Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.QPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.notInOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) (Litex.QPos (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (((0 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.numberNotPositive (M := M) (0 : ℚ) (by norm_num)) (Litex.inQPos_positive (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) _member)))
      )
  )

noncomputable def _object_w9 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))

theorem h_43 : (by
  let _atomic_wd_1_0 := (_object_w9 (M := M))
  exact ¬ Litex.In _atomic_wd_1_0 (Litex.RPos (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w9 (M := M))
          exact (Litex.notInOfSame _atomic_wd_1_0 (Litex.number (M := M) (((-2 : ℚ) : ℚ) : ℂ)) (Litex.RPos (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (((-2 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.numberNotPositive (M := M) (-2 : ℚ) (by norm_num)) (Litex.inRPos_positive (Litex.number (M := M) (((-2 : ℚ) : ℚ) : ℂ)) _member))))
      )
  )

theorem h_57 : ¬ Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.QNeg (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.notInOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (((2 : ℚ) : ℚ) : ℂ)) (Litex.QNeg (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (((2 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.numberNotNegative (M := M) (2 : ℚ) (by norm_num)) (Litex.inQNeg_negative (Litex.number (M := M) (((2 : ℚ) : ℚ) : ℂ)) _member)))
      )
  )

theorem h_72 : ¬ Litex.In (Litex.number (M := M) (1.5 : ℂ)) (Litex.ZNeg (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.notInOfSame (Litex.number (M := M) (1.5 : ℂ)) (Litex.number (M := M) (((1.5 : ℚ) : ℚ) : ℂ)) (Litex.ZNeg (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (1.5 : ℂ))).trans (congrArg M.number (by norm_num : (1.5 : ℂ) = (((1.5 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.numberNotInZOfDenominator (M := M) (1.5 : ℚ) (by norm_num)) (Litex.inZNeg_base (Litex.number (M := M) (((1.5 : ℚ) : ℚ) : ℂ)) _member)))
      )
  )

theorem h_93 : ¬ Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.RNeg (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.notInOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) (Litex.RNeg (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (((0 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.numberNotNegative (M := M) (0 : ℚ) (by norm_num)) (Litex.inRNeg_negative (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) _member)))
      )
  )

theorem h_116 : ¬ Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.QStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.notInOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) (Litex.QStar (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (((0 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.inQStar_nonzero (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) _member) (congrArg M.number (by norm_num : (((0 : ℚ) : ℚ) : ℂ) = (0 : ℂ)))))
      )
  )

theorem h_143 : ¬ Litex.In (Litex.number (M := M) (1.5 : ℂ)) (Litex.ZStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.notInOfSame (Litex.number (M := M) (1.5 : ℂ)) (Litex.number (M := M) (((1.5 : ℚ) : ℚ) : ℂ)) (Litex.ZStar (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (1.5 : ℂ))).trans (congrArg M.number (by norm_num : (1.5 : ℂ) = (((1.5 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.numberNotInZOfDenominator (M := M) (1.5 : ℚ) (by norm_num)) (Litex.inZStar_base (Litex.number (M := M) (((1.5 : ℚ) : ℚ) : ℂ)) _member)))
      )
  )

theorem h_172 : ¬ Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.RStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.notInOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) (Litex.RStar (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (((0 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.inRStar_nonzero (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) _member) (congrArg M.number (by norm_num : (((0 : ℚ) : ℚ) : ℂ) = (0 : ℂ)))))
      )
  )

theorem h_205 : ¬ Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.CStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.notInOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) (Litex.CStar (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (((0 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.inCStar_nonzero (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) _member) (congrArg M.number (by norm_num : (((0 : ℚ) : ℚ) : ℂ) = (0 : ℂ)))))
      )
  )

noncomputable def _object_w19 := (Litex.sub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))

theorem h_242 : (by
  let _atomic_wd_1_0 := (_object_w19 (M := M))
  exact ¬ Litex.In _atomic_wd_1_0 (Litex.CStar (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w19 (M := M))
          exact (Litex.notInOfSame _atomic_wd_1_0 (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) (Litex.CStar (M := M)) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) - (1 : ℂ)) = (((0 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.inCStar_nonzero (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) _member) (congrArg M.number (by norm_num : (((0 : ℚ) : ℚ) : ℂ) = (0 : ℂ))))))
      )
  )

noncomputable def _object_w20 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_273 : (by
  let _atomic_wd_1_0 := (_object_w20 (M := M))
  exact ¬ Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w20 (M := M))
          exact (Litex.notInOfSame _atomic_wd_1_0 (Litex.number (M := M) ((((1 : ℚ) / (3 : ℚ)) : ℚ) : ℂ)) (Litex.Z (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((((1 : ℚ) / (3 : ℚ)) : ℚ) : ℂ)))) (fun _member => (Litex.numberNotInZOfDenominator (M := M) ((1 : ℚ) / (3 : ℚ)) (by norm_num)) _member)))
      )
  )

theorem h_307 : (by
  let _atomic_wd_1_0 := (_object_w20 (M := M))
  exact ¬ Litex.In _atomic_wd_1_0 (Litex.N (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w20 (M := M))
          exact (Litex.notInOfSame _atomic_wd_1_0 (Litex.number (M := M) ((((1 : ℚ) / (3 : ℚ)) : ℚ) : ℂ)) (Litex.N (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) ((_object_w20 (M := M))).wd.1 ((_object_w20 (M := M))).wd.2.1 ((_object_w20 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((((1 : ℚ) / (3 : ℚ)) : ℚ) : ℂ)))) (fun _member => (Litex.numberNotInZOfDenominator (M := M) ((1 : ℚ) / (3 : ℚ)) (by norm_num)) (Litex.naturalToInteger (Litex.number (M := M) ((((1 : ℚ) / (3 : ℚ)) : ℚ) : ℂ)) _member))))
      )
  )

theorem h_342 : ¬ Litex.In (Litex.number (M := M) Complex.I) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.notInOfSame (Litex.number (M := M) Complex.I) (Litex.number (M := M) Complex.I) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I) (fun _member => (Litex.numberNotInROfImaginary Complex.I (by norm_num [Complex.ext_iff])) _member))
      )
  )

noncomputable def _object_w23 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) Complex.I))

theorem h_377 : (by
  let _atomic_wd_1_0 := (_object_w23 (M := M))
  exact ¬ Litex.In _atomic_wd_1_0 (Litex.QStar (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w23 (M := M))
          exact (Litex.notInOfSame _atomic_wd_1_0 (Litex.number (M := M) ((1 : ℂ) + Complex.I)) (Litex.QStar (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I)) (fun _member => (Litex.numberNotInROfImaginary ((1 : ℂ) + Complex.I) (by norm_num [Complex.ext_iff])) (Litex.rationalToReal (Litex.number (M := M) ((1 : ℂ) + Complex.I)) (Litex.inQStar_base (Litex.number (M := M) ((1 : ℂ) + Complex.I)) _member)))))
      )
  )

theorem h_416 : ¬ Litex.In (Litex.number (M := M) Complex.I) (Litex.NPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.notInOfSame (Litex.number (M := M) Complex.I) (Litex.number (M := M) Complex.I) (Litex.NPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I) (fun _member => (Litex.numberNotInROfImaginary Complex.I (by norm_num [Complex.ext_iff])) (Litex.naturalToReal (Litex.number (M := M) Complex.I) (Litex.inNPos_natural (Litex.number (M := M) Complex.I) _member))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_numeric_x5f_nonmembership_x2f_statement_x2e_lit
