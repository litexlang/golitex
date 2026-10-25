import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_range_x5f_sum_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_w5 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (M.divValue _raw_i1 (M.number (2 : ℂ)))) (by
  intro _raw_i1 h_15 _
  let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_15)
  have h_15 : Litex.In _value_i1 (Litex.Z (M := M)) := h_15
  change (by
    let _atomic_wd_1_0 := (Litex.div _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.integerToComplex _value_i1 h_15) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.integerToComplex _value_i1 h_15) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact (Litex.divInQ _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.integerToRational _value_i1 h_15) (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))));
(Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.rationalToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (3 : ℂ) (by
          let _aggregate := _equal_wd_1_0
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (1 : ℂ))) = ((1 : ℂ) / (2 : ℂ)) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (M.divValue _raw_i1 (M.number (2 : ℂ)))) (by
            intro _raw_i1 h_82 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_82)
            have h_82 : Litex.In _value_i1 (Litex.Z (M := M)) := h_82
            change (by
              let _atomic_wd_1_0 := (Litex.div _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.integerToComplex _value_i1 h_82) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.div _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.integerToComplex _value_i1 h_82) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.divInQ _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.integerToRational _value_i1 h_82) (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) := rfl
            have _calculated : (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number ((1 : ℂ) / (2 : ℂ)) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number ((1 : ℂ) / (2 : ℂ)))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (M.divValue _raw_i1 (M.number (2 : ℂ)))) (by
            intro _raw_i1 h_142 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_142)
            have h_142 : Litex.In _value_i1 (Litex.Z (M := M)) := h_142
            change (by
              let _atomic_wd_1_0 := (Litex.div _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.integerToComplex _value_i1 h_142) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.div _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.integerToComplex _value_i1 h_142) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.divInQ _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.integerToRational _value_i1 h_142) (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.divValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) := rfl
            have _calculated : (M.divValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = ((3 : ℂ) / (2 : ℂ)) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (M.divValue _raw_i1 (M.number (2 : ℂ)))) (by
            intro _raw_i1 h_202 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_202)
            have h_202 : Litex.In _value_i1 (Litex.Z (M := M)) := h_202
            change (by
              let _atomic_wd_1_0 := (Litex.div _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.integerToComplex _value_i1 h_202) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.div _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.integerToComplex _value_i1 h_202) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.divInQ _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.integerToRational _value_i1 h_202) (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num)) (_atomic_wd_1_0).wd.2.2))));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) := rfl
            have _calculated : (M.divValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) = M.number ((3 : ℂ) / (2 : ℂ)) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number ((3 : ℂ) / (2 : ℂ)))
          apply Litex.rangeAggregateDenote _aggregate (1 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (3 : ℂ)
          have _indices : Finset.Icc (1 : ℤ) (3 : ℤ) = {(1 : ℤ), (2 : ℤ), (3 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2]) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_rational_x5f_range_x5f_sum_x2f_statement_x2e_lit
