import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_aggregate_x5f_calls_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.Z (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInZ _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))))
theorem h_57 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_58 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_82 : (by
  let _equal_wd_1_0 := (Litex.rangeAggregate false (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)))) (h_57 (M := M))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.rangeAggregate false (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)))) (h_57 (M := M))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) (((Eq.refl (Litex.denote (Litex.rangeAggregate false (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)))) (h_57 (M := M))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k))))).trans (show (Litex.denote (Litex.rangeAggregate false (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)))) (h_57 (M := M))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k))) = M.number (9 : ℂ) from (by
          let _aggregate := (Litex.rangeAggregate false (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)))) (h_57 (M := M))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k))
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (1 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro)
            let _literal := (_object_i1 (M := M))
            have _head : Litex.Same _call.val.function _literal := (h_58 (M := M))
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) := rfl
            have _calculated : (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro)
            let _literal := (_object_i1 (M := M))
            have _head : Litex.Same _call.val.function _literal := (h_58 (M := M))
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) := rfl
            have _calculated : (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (4 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro)
            let _literal := (_object_i1 (M := M))
            have _head : Litex.Same _call.val.function _literal := (h_58 (M := M))
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.addValue (M.number (3 : ℂ)) (M.number (1 : ℂ))) := rfl
            have _calculated : (M.addValue (M.number (3 : ℂ)) (M.number (1 : ℂ))) = M.number (4 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (4 : ℂ))
          apply Litex.rangeAggregateDenote _aggregate (1 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (9 : ℂ)
          have _indices : Finset.Icc (1 : ℤ) (3 : ℤ) = {(1 : ℤ), (2 : ℤ), (3 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num : (9 : ℂ) = (9 : ℂ)))).symm)))
      )
  )

theorem h_103 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl)) (((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))))).trans (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) = (M.addValue (M.number (3 : ℂ)) (M.number (1 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro)
          let _litex_formula := (_object_i1 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_58 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.addValue (M.number (3 : ℂ)) (M.number (1 : ℂ))) from congrArg (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))))
        )).trans (((Eq.refl (M.addValue (M.number (3 : ℂ)) (M.number (1 : ℂ))))).trans (show (M.addValue (M.number (3 : ℂ)) (M.number (1 : ℂ))) = M.number (4 : ℂ) from ((congrArg₂ M.addValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (3 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))).symm)))
      )
  )

theorem h_107 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_57 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_103 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_aggregate_x5f_calls_x2f_statement_x2e_lit
