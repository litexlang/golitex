import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_range_x5f_aggregates_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_86 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
  let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
    intro _raw_i1 h_100 _
    let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_100)
    have h_100 : Litex.In _value_i1 (Litex.Z (M := M)) := h_100
    change Litex.In _value_i1 (Litex.Z (M := M))
    exact h_100));
  (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_100 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_100)
          have h_100 : Litex.In _value_i1 (Litex.Z (M := M)) := h_100
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_100));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) (((Eq.refl (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_14 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
          have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_14));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))))).trans (show (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_14 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
          have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_14));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))) = M.number (6 : ℂ) from (by
          let _aggregate := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_14 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
            have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_14));
          (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (1 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_39 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_39)
            have h_39 : Litex.In _value_i1 (Litex.Z (M := M)) := h_39
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_39));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_39 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_39)
            have h_39 : Litex.In _value_i1 (Litex.Z (M := M)) := h_39
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_39))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (1 : ℂ)) := rfl
            have _calculated : (M.number (1 : ℂ)) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_59 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_59)
            have h_59 : Litex.In _value_i1 (Litex.Z (M := M)) := h_59
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_59));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_59 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_59)
            have h_59 : Litex.In _value_i1 (Litex.Z (M := M)) := h_59
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_59))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := rfl
            have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_79 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_79)
            have h_79 : Litex.In _value_i1 (Litex.Z (M := M)) := h_79
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_79));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_79 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_79)
            have h_79 : Litex.In _value_i1 (Litex.Z (M := M)) := h_79
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_79))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := rfl
            have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
          apply Litex.rangeAggregateDenote _aggregate (1 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (6 : ℂ)
          have _indices : Finset.Icc (1 : ℤ) (3 : ℤ) = {(1 : ℤ), (2 : ℤ), (3 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = (6 : ℂ)))).symm)))
      )
  )

noncomputable def _object_w12 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
  intro _raw_i2 h_126 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_126)
  have h_126 : Litex.In _value_i2 (Litex.Z (M := M)) := h_126
  change Litex.In _value_i2 (Litex.Z (M := M))
  exact h_126));
(Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))

theorem h_112 : (by
  let _equal_wd_1_0 := (_object_w12 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w12 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) ((show (Litex.denote _equal_wd_1_0) = M.number (6 : ℂ) from (by
          let _aggregate := _equal_wd_1_0
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (1 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
            intro _raw_i2 h_153 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_153)
            have h_153 : Litex.In _value_i2 (Litex.Z (M := M)) := h_153
            change Litex.In _value_i2 (Litex.Z (M := M))
            exact h_153));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (1 : ℂ)) := rfl
            have _calculated : (M.number (1 : ℂ)) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
            intro _raw_i2 h_173 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_173)
            have h_173 : Litex.In _value_i2 (Litex.Z (M := M)) := h_173
            change Litex.In _value_i2 (Litex.Z (M := M))
            exact h_173));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := rfl
            have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
            intro _raw_i2 h_193 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_193)
            have h_193 : Litex.In _value_i2 (Litex.Z (M := M)) := h_193
            change Litex.In _value_i2 (Litex.Z (M := M))
            exact h_193));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := rfl
            have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
          apply Litex.rangeAggregateDenote _aggregate (1 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (6 : ℂ)
          have _indices : Finset.Icc (1 : ℤ) (3 : ℤ) = {(1 : ℤ), (2 : ℤ), (3 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = (6 : ℂ)))).symm)))
      )
  )

theorem h_305 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
  let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
    intro _raw_i3 h_319 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_319)
    have h_319 : Litex.In _value_i3 (Litex.Z (M := M)) := h_319
    change Litex.In _value_i3 (Litex.Z (M := M))
    exact h_319));
  (Litex.rangeAggregate true _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
          intro _raw_i3 h_319 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_319)
          have h_319 : Litex.In _value_i3 (Litex.Z (M := M)) := h_319
          change Litex.In _value_i3 (Litex.Z (M := M))
          exact h_319));
        (Litex.rangeAggregate true _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) (((Eq.refl (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
          intro _raw_i3 h_213 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_213)
          have h_213 : Litex.In _value_i3 (Litex.Z (M := M)) := h_213
          change Litex.In _value_i3 (Litex.Z (M := M))
          exact h_213));
        (Litex.rangeAggregate true _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))))).trans (show (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
          intro _raw_i3 h_213 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_213)
          have h_213 : Litex.In _value_i3 (Litex.Z (M := M)) := h_213
          change Litex.In _value_i3 (Litex.Z (M := M))
          exact h_213));
        (Litex.rangeAggregate true _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))) = M.number (120 : ℂ) from (by
          let _aggregate := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_213 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_213)
            have h_213 : Litex.In _value_i3 (Litex.Z (M := M)) := h_213
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_213));
          (Litex.rangeAggregate true _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_238 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_238)
            have h_238 : Litex.In _value_i3 (Litex.Z (M := M)) := h_238
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_238));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_238 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_238)
            have h_238 : Litex.In _value_i3 (Litex.Z (M := M)) := h_238
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_238))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := rfl
            have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_258 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_258)
            have h_258 : Litex.In _value_i3 (Litex.Z (M := M)) := h_258
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_258));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_258 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_258)
            have h_258 : Litex.In _value_i3 (Litex.Z (M := M)) := h_258
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_258))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := rfl
            have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (4 : ℂ))) = (4 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_278 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_278)
            have h_278 : Litex.In _value_i3 (Litex.Z (M := M)) := h_278
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_278));
          let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_278 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_278)
            have h_278 : Litex.In _value_i3 (Litex.Z (M := M)) := h_278
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_278))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (4 : ℂ)) := rfl
            have _calculated : (M.number (4 : ℂ)) = M.number (4 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (4 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (4 : ℂ))
          have _aggregate_term_3 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (5 : ℂ))) = (5 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_298 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_298)
            have h_298 : Litex.In _value_i3 (Litex.Z (M := M)) := h_298
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_298));
          let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_298 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_298)
            have h_298 : Litex.In _value_i3 (Litex.Z (M := M)) := h_298
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_298))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (5 : ℂ)) := rfl
            have _calculated : (M.number (5 : ℂ)) = M.number (5 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (5 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (5 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (5 : ℂ))
          apply Litex.rangeAggregateDenote _aggregate (2 : ℤ) (5 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)).trans (congrArg M.number (by norm_num))) (120 : ℂ)
          have _indices : Finset.Icc (2 : ℤ) (5 : ℤ) = {(2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2, _aggregate_term_3]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (120 : ℂ))).trans (congrArg M.number (by norm_num : (120 : ℂ) = (120 : ℂ)))).symm)))
      )
  )

noncomputable def _object_w26 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
  intro _raw_i4 h_345 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_345)
  have h_345 : Litex.In _value_i4 (Litex.Z (M := M)) := h_345
  change Litex.In _value_i4 (Litex.Z (M := M))
  exact h_345));
(Litex.rangeAggregate true _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))

theorem h_331 : (by
  let _equal_wd_1_0 := (_object_w26 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w26 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) ((show (Litex.denote _equal_wd_1_0) = M.number (120 : ℂ) from (by
          let _aggregate := _equal_wd_1_0
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
            intro _raw_i4 h_372 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_372)
            have h_372 : Litex.In _value_i4 (Litex.Z (M := M)) := h_372
            change Litex.In _value_i4 (Litex.Z (M := M))
            exact h_372));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := rfl
            have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
            intro _raw_i4 h_392 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_392)
            have h_392 : Litex.In _value_i4 (Litex.Z (M := M)) := h_392
            change Litex.In _value_i4 (Litex.Z (M := M))
            exact h_392));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := rfl
            have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (4 : ℂ))) = (4 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
            intro _raw_i4 h_412 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_412)
            have h_412 : Litex.In _value_i4 (Litex.Z (M := M)) := h_412
            change Litex.In _value_i4 (Litex.Z (M := M))
            exact h_412));
          let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (4 : ℂ)) := rfl
            have _calculated : (M.number (4 : ℂ)) = M.number (4 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (4 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (4 : ℂ))
          have _aggregate_term_3 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (5 : ℂ))) = (5 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
            intro _raw_i4 h_432 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_432)
            have h_432 : Litex.In _value_i4 (Litex.Z (M := M)) := h_432
            change Litex.In _value_i4 (Litex.Z (M := M))
            exact h_432));
          let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (5 : ℂ)) := rfl
            have _calculated : (M.number (5 : ℂ)) = M.number (5 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (5 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (5 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (5 : ℂ))
          apply Litex.rangeAggregateDenote _aggregate (2 : ℤ) (5 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)).trans (congrArg M.number (by norm_num))) (120 : ℂ)
          have _indices : Finset.Icc (2 : ℤ) (5 : ℤ) = {(2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2, _aggregate_term_3]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (120 : ℂ))).trans (congrArg M.number (by norm_num : (120 : ℂ) = (120 : ℂ)))).symm)))
      )
  )

theorem h_898 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
    intro _raw_i5 h_913 _
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_913)
    have h_913 : Litex.In _value_i5 (Litex.Z (M := M)) := h_913
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_913) (Litex.integerToComplex _value_i5 h_913))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_913) (Litex.integerToComplex _value_i5 h_913))
      exact (Litex.mulInZ _value_i5 _value_i5 h_913 h_913))));
  (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True)) (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (by
    let _atomic_wd_1_0 := _wd_1_0
    exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _atomic_wd_1_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
      let _atomic_wd_2_0 := _atomic_wd_1_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) = (-2 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
      let _atomic_wd_2_0 := _atomic_wd_1_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (10 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
          intro _raw_i5 h_913 _
          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_913)
          have h_913 : Litex.In _value_i5 (Litex.Z (M := M)) := h_913
          change (by
            let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_913) (Litex.integerToComplex _value_i5 h_913))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_913) (Litex.integerToComplex _value_i5 h_913))
            exact (Litex.mulInZ _value_i5 _value_i5 h_913 h_913))));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True)) (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (by
          let _atomic_wd_1_0 := _wd_1_0
          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 _wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) = (-2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (10 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (10 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) (((Eq.refl (Litex.denote (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
          intro _raw_i5 h_453 _
          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_453)
          have h_453 : Litex.In _value_i5 (Litex.Z (M := M)) := h_453
          change (by
            let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_453) (Litex.integerToComplex _value_i5 h_453))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_453) (Litex.integerToComplex _value_i5 h_453))
            exact (Litex.mulInZ _value_i5 _value_i5 h_453 h_453))));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True)) (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (by
          let _atomic_wd_1_0 := _wd_1_0
          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 _wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) = (-2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))))).trans (show (Litex.denote (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
          intro _raw_i5 h_453 _
          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_453)
          have h_453 : Litex.In _value_i5 (Litex.Z (M := M)) := h_453
          change (by
            let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_453) (Litex.integerToComplex _value_i5 h_453))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_453) (Litex.integerToComplex _value_i5 h_453))
            exact (Litex.mulInZ _value_i5 _value_i5 h_453 h_453))));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True)) (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (by
          let _atomic_wd_1_0 := _wd_1_0
          exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 _wd_1_1 (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) = (-2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))) = M.number (10 : ℂ) from (by
          let _aggregate := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
            intro _raw_i5 h_453 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_453)
            have h_453 : Litex.In _value_i5 (Litex.Z (M := M)) := h_453
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_453) (Litex.integerToComplex _value_i5 h_453))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_453) (Litex.integerToComplex _value_i5 h_453))
              exact (Litex.mulInZ _value_i5 _value_i5 h_453 h_453))));
          (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True)) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (by
            let _atomic_wd_1_0 := _wd_1_0
            exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 _wd_1_1 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) = (-2 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (-2 : ℂ))) = (4 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
            intro _raw_i5 h_536 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_536)
            have h_536 : Litex.In _value_i5 (Litex.Z (M := M)) := h_536
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_536) (Litex.integerToComplex _value_i5 h_536))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_536) (Litex.integerToComplex _value_i5 h_536))
              exact (Litex.mulInZ _value_i5 _value_i5 h_536 h_536))));
          let _wd_1_1 := (Litex.number (M := M) (-2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-2 : ℂ) (-2 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
            intro _raw_i5 h_536 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_536)
            have h_536 : Litex.In _value_i5 (Litex.Z (M := M)) := h_536
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_536) (Litex.integerToComplex _value_i5 h_536))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_536) (Litex.integerToComplex _value_i5 h_536))
              exact (Litex.mulInZ _value_i5 _value_i5 h_536 h_536))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.mulValue (M.number (-2 : ℂ)) (M.number (-2 : ℂ))) := rfl
            have _calculated : (M.mulValue (M.number (-2 : ℂ)) (M.number (-2 : ℂ))) = M.number (4 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (-2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))).trans (congrArg M.number (by norm_num : (-2 : ℂ) = (-2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (4 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (-1 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
            intro _raw_i5 h_611 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_611)
            have h_611 : Litex.In _value_i5 (Litex.Z (M := M)) := h_611
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_611) (Litex.integerToComplex _value_i5 h_611))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_611) (Litex.integerToComplex _value_i5 h_611))
              exact (Litex.mulInZ _value_i5 _value_i5 h_611 h_611))));
          let _wd_1_1 := (Litex.number (M := M) (-1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-1 : ℂ) (-1 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
            intro _raw_i5 h_611 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_611)
            have h_611 : Litex.In _value_i5 (Litex.Z (M := M)) := h_611
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_611) (Litex.integerToComplex _value_i5 h_611))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_611) (Litex.integerToComplex _value_i5 h_611))
              exact (Litex.mulInZ _value_i5 _value_i5 h_611 h_611))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.mulValue (M.number (-1 : ℂ)) (M.number (-1 : ℂ))) := rfl
            have _calculated : (M.mulValue (M.number (-1 : ℂ)) (M.number (-1 : ℂ))) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (-1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num : (-1 : ℂ) = (-1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (0 : ℂ))) = (0 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
            intro _raw_i5 h_686 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_686)
            have h_686 : Litex.In _value_i5 (Litex.Z (M := M)) := h_686
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_686) (Litex.integerToComplex _value_i5 h_686))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_686) (Litex.integerToComplex _value_i5 h_686))
              exact (Litex.mulInZ _value_i5 _value_i5 h_686 h_686))));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
            intro _raw_i5 h_686 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_686)
            have h_686 : Litex.In _value_i5 (Litex.Z (M := M)) := h_686
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_686) (Litex.integerToComplex _value_i5 h_686))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_686) (Litex.integerToComplex _value_i5 h_686))
              exact (Litex.mulInZ _value_i5 _value_i5 h_686 h_686))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) := rfl
            have _calculated : (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) = M.number (0 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (0 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (0 : ℂ))
          have _aggregate_term_3 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (1 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
            intro _raw_i5 h_761 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_761)
            have h_761 : Litex.In _value_i5 (Litex.Z (M := M)) := h_761
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_761) (Litex.integerToComplex _value_i5 h_761))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_761) (Litex.integerToComplex _value_i5 h_761))
              exact (Litex.mulInZ _value_i5 _value_i5 h_761 h_761))));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
            intro _raw_i5 h_761 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_761)
            have h_761 : Litex.In _value_i5 (Litex.Z (M := M)) := h_761
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_761) (Litex.integerToComplex _value_i5 h_761))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_761) (Litex.integerToComplex _value_i5 h_761))
              exact (Litex.mulInZ _value_i5 _value_i5 h_761 h_761))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) := rfl
            have _calculated : (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_4 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (4 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
            intro _raw_i5 h_836 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_836)
            have h_836 : Litex.In _value_i5 (Litex.Z (M := M)) := h_836
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_836) (Litex.integerToComplex _value_i5 h_836))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_836) (Litex.integerToComplex _value_i5 h_836))
              exact (Litex.mulInZ _value_i5 _value_i5 h_836 h_836))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (M.mulValue _raw_i5 _raw_i5)) (by
            intro _raw_i5 h_836 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_836)
            have h_836 : Litex.In _value_i5 (Litex.Z (M := M)) := h_836
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_836) (Litex.integerToComplex _value_i5 h_836))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i5 _value_i5 (Litex.integerToComplex _value_i5 h_836) (Litex.integerToComplex _value_i5 h_836))
              exact (Litex.mulInZ _value_i5 _value_i5 h_836 h_836))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) := rfl
            have _calculated : (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) = M.number (4 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (4 : ℂ))
          apply Litex.rangeAggregateDenote _aggregate (-2 : ℤ) (2 : ℤ) ((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)).trans (congrArg M.number (by norm_num))) (10 : ℂ)
          have _indices : Finset.Icc (-2 : ℤ) (2 : ℤ) = {(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2, _aggregate_term_3, _aggregate_term_4]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (10 : ℂ))).trans (congrArg M.number (by norm_num : (10 : ℂ) = (10 : ℂ)))).symm)))
      )
  )

noncomputable def _object_w42 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.mulValue _raw_i6 _raw_i6)) (by
  intro _raw_i6 h_998 _
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_998)
  have h_998 : Litex.In _value_i6 (Litex.Z (M := M)) := h_998
  change (by
    let _atomic_wd_1_0 := (Litex.mul _value_i6 _value_i6 (Litex.integerToComplex _value_i6 h_998) (Litex.integerToComplex _value_i6 h_998))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.mul _value_i6 _value_i6 (Litex.integerToComplex _value_i6 h_998) (Litex.integerToComplex _value_i6 h_998))
    exact (Litex.mulInZ _value_i6 _value_i6 h_998 h_998))));
(Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True)) (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (by
  let _atomic_wd_1_0 := _wd_1_0
  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 _wd_1_1 (by
    let _atomic_wd_2_0 := _atomic_wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
    let _atomic_wd_2_0 := _atomic_wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) = (-2 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
    let _atomic_wd_2_0 := _atomic_wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))

theorem h_983 : (by
  let _equal_wd_1_0 := (_object_w42 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (10 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w42 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (10 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (10 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) ((show (Litex.denote _equal_wd_1_0) = M.number (10 : ℂ) from (by
          let _aggregate := _equal_wd_1_0
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (-2 : ℂ))) = (4 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.mulValue _raw_i6 _raw_i6)) (by
            intro _raw_i6 h_1083 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1083)
            have h_1083 : Litex.In _value_i6 (Litex.Z (M := M)) := h_1083
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i6 _value_i6 (Litex.integerToComplex _value_i6 h_1083) (Litex.integerToComplex _value_i6 h_1083))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i6 _value_i6 (Litex.integerToComplex _value_i6 h_1083) (Litex.integerToComplex _value_i6 h_1083))
              exact (Litex.mulInZ _value_i6 _value_i6 h_1083 h_1083))));
          let _wd_1_1 := (Litex.number (M := M) (-2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-2 : ℂ) (-2 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.mulValue (M.number (-2 : ℂ)) (M.number (-2 : ℂ))) := rfl
            have _calculated : (M.mulValue (M.number (-2 : ℂ)) (M.number (-2 : ℂ))) = M.number (4 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (-2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-2 : ℂ))).trans (congrArg M.number (by norm_num : (-2 : ℂ) = (-2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (4 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (-1 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.mulValue _raw_i6 _raw_i6)) (by
            intro _raw_i6 h_1158 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1158)
            have h_1158 : Litex.In _value_i6 (Litex.Z (M := M)) := h_1158
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i6 _value_i6 (Litex.integerToComplex _value_i6 h_1158) (Litex.integerToComplex _value_i6 h_1158))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i6 _value_i6 (Litex.integerToComplex _value_i6 h_1158) (Litex.integerToComplex _value_i6 h_1158))
              exact (Litex.mulInZ _value_i6 _value_i6 h_1158 h_1158))));
          let _wd_1_1 := (Litex.number (M := M) (-1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-1 : ℂ) (-1 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.mulValue (M.number (-1 : ℂ)) (M.number (-1 : ℂ))) := rfl
            have _calculated : (M.mulValue (M.number (-1 : ℂ)) (M.number (-1 : ℂ))) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (-1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num : (-1 : ℂ) = (-1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (0 : ℂ))) = (0 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.mulValue _raw_i6 _raw_i6)) (by
            intro _raw_i6 h_1233 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1233)
            have h_1233 : Litex.In _value_i6 (Litex.Z (M := M)) := h_1233
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i6 _value_i6 (Litex.integerToComplex _value_i6 h_1233) (Litex.integerToComplex _value_i6 h_1233))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i6 _value_i6 (Litex.integerToComplex _value_i6 h_1233) (Litex.integerToComplex _value_i6 h_1233))
              exact (Litex.mulInZ _value_i6 _value_i6 h_1233 h_1233))));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) := rfl
            have _calculated : (M.mulValue (M.number (0 : ℂ)) (M.number (0 : ℂ))) = M.number (0 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (0 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (0 : ℂ))
          have _aggregate_term_3 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (1 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.mulValue _raw_i6 _raw_i6)) (by
            intro _raw_i6 h_1308 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1308)
            have h_1308 : Litex.In _value_i6 (Litex.Z (M := M)) := h_1308
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i6 _value_i6 (Litex.integerToComplex _value_i6 h_1308) (Litex.integerToComplex _value_i6 h_1308))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i6 _value_i6 (Litex.integerToComplex _value_i6 h_1308) (Litex.integerToComplex _value_i6 h_1308))
              exact (Litex.mulInZ _value_i6 _value_i6 h_1308 h_1308))));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) := rfl
            have _calculated : (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_4 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (4 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.mulValue _raw_i6 _raw_i6)) (by
            intro _raw_i6 h_1383 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1383)
            have h_1383 : Litex.In _value_i6 (Litex.Z (M := M)) := h_1383
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i6 _value_i6 (Litex.integerToComplex _value_i6 h_1383) (Litex.integerToComplex _value_i6 h_1383))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i6 _value_i6 (Litex.integerToComplex _value_i6 h_1383) (Litex.integerToComplex _value_i6 h_1383))
              exact (Litex.mulInZ _value_i6 _value_i6 h_1383 h_1383))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) := rfl
            have _calculated : (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) = M.number (4 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (4 : ℂ))
          apply Litex.rangeAggregateDenote _aggregate (-2 : ℤ) (2 : ℤ) ((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)).trans (congrArg M.number (by norm_num))) (10 : ℂ)
          have _indices : Finset.Icc (-2 : ℤ) (2 : ℤ) = {(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2, _aggregate_term_3, _aggregate_term_4]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (10 : ℂ))).trans (congrArg M.number (by norm_num : (10 : ℂ) = (10 : ℂ)))).symm)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_range_x5f_aggregates_x2f_statement_x2e_lit
