import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_logarithm_x5f_functions_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (fun (_raw_i2 : M.Value) => (M.divValue (Litex.realUnaryValue (M := M) Real.log _raw_i2) (Litex.realUnaryValue (M := M) Real.log (M.number (2 : ℂ))))) (by
  intro _raw_i2 h_14 _positive_i2
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_14, _positive_i2⟩)
  have h_15 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i2 h_14)
        )
    )
  have h_16 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_15)
        )
    )
  have h_17 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_15) _litex_zero.symm)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.log (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.inRPos_real _value_i2 h_14) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num))) h_15 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (2 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.log (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.inRPos_real _value_i2 h_14) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num))) h_15 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (2 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)))
    exact (Litex.logInR _atomic_wd_1_0))))
theorem h_126 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_127 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_134 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (_object_i1 (M := M)) (Litex.number (M := M) (8 : ℂ)) (h_126 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (8 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (8 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (8 : ℂ) (8 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (8 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (8 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (8 : ℂ) (8 : ℝ) (by norm_num) (by norm_num)))).2)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (_object_i1 (M := M)) (Litex.number (M := M) (8 : ℂ)) (h_126 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (8 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (8 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (8 : ℂ) (8 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (8 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (8 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (8 : ℂ) (8 : ℝ) (by norm_num) (by norm_num)))).2);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (8 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (8 : ℂ)) = (M.number (8 : ℂ)) from rfl)) (((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (8 : ℂ))))).trans (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (8 : ℂ))) = ((fun _base _arg => M.divValue (Litex.realUnaryValue (M := M) Real.log _arg) (Litex.realUnaryValue (M := M) Real.log _base)) (M.number (2 : ℂ)) (M.number (8 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (_object_i1 (M := M)) (Litex.number (M := M) (8 : ℂ)) (h_126 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (8 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (8 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (8 : ℂ) (8 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (8 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (8 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (8 : ℂ) (8 : ℝ) (by norm_num) (by norm_num)))).2)
          let _litex_formula := (_object_i1 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_127 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (_object_i1 (M := M)) (Litex.number (M := M) (8 : ℂ)) (h_126 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (8 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (8 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (8 : ℂ) (8 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (8 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (8 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (8 : ℂ) (8 : ℝ) (by norm_num) (by norm_num)))).2) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (8 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (8 : ℂ)) = (M.number (8 : ℂ)) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = ((fun _base _arg => M.divValue (Litex.realUnaryValue (M := M) Real.log _arg) (Litex.realUnaryValue (M := M) Real.log _base)) (M.number (2 : ℂ)) (M.number (8 : ℂ))) from congrArg (fun (_raw_i2 : M.Value) => (M.divValue (Litex.realUnaryValue (M := M) Real.log _raw_i2) (Litex.realUnaryValue (M := M) Real.log (M.number (2 : ℂ))))) (show Litex.denote (Litex.number (M := M) (8 : ℂ)) = (M.number (8 : ℂ)) from rfl))))
        )).trans (((Eq.refl ((fun _base _arg => M.divValue (Litex.realUnaryValue (M := M) Real.log _arg) (Litex.realUnaryValue (M := M) Real.log _base)) (M.number (2 : ℂ)) (M.number (8 : ℂ))))).trans (show ((fun _base _arg => M.divValue (Litex.realUnaryValue (M := M) Real.log _arg) (Litex.realUnaryValue (M := M) Real.log _base)) (M.number (2 : ℂ)) (M.number (8 : ℂ))) = M.number (3 : ℂ) from (congrArg₂ (fun _base _arg => M.divValue (Litex.realUnaryValue (M := M) Real.log _arg) (Litex.realUnaryValue (M := M) Real.log _base)) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (show (M.number (8 : ℂ)) = M.number (8 : ℂ) from (congrArg M.number (show (8 : ℂ) = (8 : ℂ) from by norm_num)))).trans (by
          have _base_cast : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ) := by norm_num
          have _arg_cast : (8 : ℂ) = (((8 : ℝ) : ℝ) : ℂ) := by norm_num
          have _base_nonzero : ((Real.log (2 : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 1))
          have _value : Real.log (8 : ℝ) / Real.log (2 : ℝ) = (3 : ℝ) := (Litex.rationalLogValue (2 : ℝ) (8 : ℝ) (3 : ℤ) (1 : ℕ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num)
          have _base := (congrArg (Litex.realUnaryValue (M := M) Real.log) (congrArg M.number _base_cast)).trans (Litex.realUnaryValue_number (M := M) Real.log (2 : ℝ))
          have _arg := (congrArg (Litex.realUnaryValue (M := M) Real.log) (congrArg M.number _arg_cast)).trans (Litex.realUnaryValue_number (M := M) Real.log (8 : ℝ))
          exact (congrArg₂ M.divValue _arg _base).trans ((M.div_numbers _ _ _base_nonzero).trans (congrArg M.number (by rw [← Complex.ofReal_div, _value]; norm_num)))))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))).symm)))
      )
  )

theorem h_138 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (_object_i1 (M := M)) (Litex.number (M := M) (8 : ℂ)) (h_126 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (8 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (8 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (8 : ℂ) (8 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (8 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (8 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (8 : ℂ) (8 : ℝ) (by norm_num) (by norm_num)))).2)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_134 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_logarithm_x5f_functions_x2f_statement_x2e_lit
