import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_negative_x5f_integer_x5f_exponent_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_i1 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
theorem h_5 : Litex.In (_object_i1 (M := M)) (Litex.Z (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (3 : ℂ)) (-3 : ℤ) (by norm_num))))
      )
  )
theorem h_6 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))))
      )
  )

theorem h_2060 : (by
  let _equal_wd_1_0 := (Litex.powInt (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Classical.choose ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))) (Litex.numberInC (M := M) (2 : ℂ)) (h_5 (M := M)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))))
  let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.powInt (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Classical.choose ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))) (Litex.numberInC (M := M) (2 : ℂ)) (h_5 (M := M)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))));
        let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (M.powValue (M.number (2 : ℂ)) (Litex.denote (_object_i1 (M := M)))) from congrArg₂ M.powValue (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (((congrArg₂ M.powValue (Eq.refl (M.number (2 : ℂ))) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (h_6 (M := M))) (show Litex.denote (_object_i1 (M := M)) = (M.negValue (M.number (3 : ℂ))) from Eq.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = (-3 : ℂ)))) (Eq.symm (show (M.negValue (M.number (3 : ℂ))) = M.number (-3 : ℂ) from ((congrArg M.negValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.neg_numbers (3 : ℂ)).trans (congrArg M.number (by norm_num)))))))))).trans (show (M.powValue (M.number (2 : ℂ)) (M.negValue (M.number (3 : ℂ)))) = M.number ((1 : ℂ) / (8 : ℂ)) from ((congrArg₂ M.powValue (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (show (M.negValue (M.number (3 : ℂ))) = M.number (-3 : ℂ) from ((congrArg M.negValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.neg_numbers (3 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans ((show M.powValue (M.number (2 : ℂ)) (M.number (-3 : ℂ)) = M.number ((2 : ℂ) ^ (-3 : ℤ)) from by simpa only [Int.cast_neg, Int.cast_ofNat] using M.pow_numbers_int (2 : ℂ) (-3) (by norm_num)).trans (congrArg M.number (by norm_num)))))))).trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (8 : ℂ)) = ((1 : ℂ) / (8 : ℂ))))).symm)))
      )
  )

theorem h_4156 : Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (Litex.RPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4121 : (by
          let _atomic_wd_1_1 := (Litex.powInt (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Classical.choose ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))) (Litex.numberInC (M := M) (2 : ℂ)) (h_5 (M := M)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))))
          exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
          let _atomic_wd_1_1 := (Litex.powInt (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Classical.choose ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))) (Litex.numberInC (M := M) (2 : ℂ)) (h_5 (M := M)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))))
          exact (Litex.powStructuralPositiveOfPositive _atomic_wd_1_1 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
          have h_4145 : Litex.In (_object_i1 (M := M)) (Litex.R (M := M)) := (Litex.integerToReal (_object_i1 (M := M)) (h_5 (M := M)))
          exact Litex.inOfSame (Litex.powInt (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Classical.choose ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))) (Litex.numberInC (M := M) (2 : ℂ)) (h_5 (M := M)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M))))) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) (h_2060 (M := M)) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (Litex.powInt (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Classical.choose ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))) (Litex.numberInC (M := M) (2 : ℂ)) (h_5 (M := M)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M))))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_4121; exact (M.real_members (Litex.denote (Litex.powInt (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Classical.choose ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))) (Litex.numberInC (M := M) (2 : ℂ)) (h_5 (M := M)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M))))))).mpr ⟨_litex_real, _litex_value⟩) h_4121)
        )
      )
  )

theorem h_4157 : (by
  let _equal_wd_1_0 := (Litex.powInt (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Classical.choose ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))) (Litex.numberInC (M := M) (2 : ℂ)) (h_5 (M := M)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))))
  let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_2060 (M := M))
      )
  )

theorem h_4211 : Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (Litex.RPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4159 : (by
          let _atomic_wd_1_1 := (Litex.powInt (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Classical.choose ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))) (Litex.numberInC (M := M) (2 : ℂ)) (h_5 (M := M)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))))
          exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) := (by
          let _atomic_wd_1_1 := (Litex.powInt (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Classical.choose ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))) (Litex.numberInC (M := M) (2 : ℂ)) (h_5 (M := M)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))))
          exact (Litex.powStructuralPositiveOfPositive _atomic_wd_1_1 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
          have h_4196 : Litex.In (_object_i1 (M := M)) (Litex.R (M := M)) := (Litex.integerToReal (_object_i1 (M := M)) (h_5 (M := M)))
          exact Litex.inOfSame (Litex.powInt (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Classical.choose ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))) (Litex.numberInC (M := M) (2 : ℂ)) (h_5 (M := M)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M))))) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (Litex.RPos (M := M)) (Litex.RPos (M := M)) (h_4157 (M := M)) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.inRPos_intro (Litex.powInt (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Classical.choose ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))) (Litex.numberInC (M := M) (2 : ℂ)) (h_5 (M := M)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M))))) (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_4159; exact (M.real_members (Litex.denote (Litex.powInt (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (Classical.choose ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M)))) (Litex.numberInC (M := M) (2 : ℂ)) (h_5 (M := M)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Classical.choose_spec ((M.integer_members (Litex.denote (_object_i1 (M := M)))).mp (h_5 (M := M))))))).mpr ⟨_litex_real, _litex_value⟩) h_4159)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_negative_x5f_integer_x5f_exponent_x2f_statement_x2e_lit
