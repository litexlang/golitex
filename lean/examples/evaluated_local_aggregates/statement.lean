import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_aggregates_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

include M in
private theorem _sketch_1 : True := by
  have h_87 : (by
    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
    let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
    let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
      intro _raw_i1 h_101 _
      let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_101)
      have h_101 : Litex.In _value_i1 (Litex.Z (M := M)) := h_101
      change Litex.In _value_i1 (Litex.Z (M := M))
      exact h_101));
    (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_101 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_101)
            have h_101 : Litex.In _value_i1 (Litex.Z (M := M)) := h_101
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_101));
          (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)));
          (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) (((Eq.refl (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_15 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_15)
            have h_15 : Litex.In _value_i1 (Litex.Z (M := M)) := h_15
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_15));
          (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))))).trans (show (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_15 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_15)
            have h_15 : Litex.In _value_i1 (Litex.Z (M := M)) := h_15
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_15));
          (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))) = M.number (9 : ℂ) from (by
            let _aggregate := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
            let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
            let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
              intro _raw_i1 h_15 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_15)
              have h_15 : Litex.In _value_i1 (Litex.Z (M := M)) := h_15
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_15));
            (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
            have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
              let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
              intro _raw_i1 h_40 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_40)
              have h_40 : Litex.In _value_i1 (Litex.Z (M := M)) := h_40
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_40));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
              let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
              intro _raw_i1 h_40 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_40)
              have h_40 : Litex.In _value_i1 (Litex.Z (M := M)) := h_40
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_40))
              have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
              have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
              have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
              have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := rfl
              have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
              exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
            have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
              let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
              intro _raw_i1 h_60 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_60)
              have h_60 : Litex.In _value_i1 (Litex.Z (M := M)) := h_60
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_60));
            let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
            (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
              let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
              intro _raw_i1 h_60 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_60)
              have h_60 : Litex.In _value_i1 (Litex.Z (M := M)) := h_60
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_60))
              have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
              have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
              have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
              have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := rfl
              have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
              exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
            have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (4 : ℂ))) = (4 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
              let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
              intro _raw_i1 h_80 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_80)
              have h_80 : Litex.In _value_i1 (Litex.Z (M := M)) := h_80
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_80));
            let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
            (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) True.intro))
              let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
              intro _raw_i1 h_80 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_80)
              have h_80 : Litex.In _value_i1 (Litex.Z (M := M)) := h_80
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_80))
              have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
              have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
              have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
              have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (4 : ℂ)) := rfl
              have _calculated : (M.number (4 : ℂ)) = M.number (4 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              have _argument : Litex.denote _call.val.argument = M.number (4 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))
              exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (4 : ℂ))
            apply Litex.rangeAggregateDenote _aggregate (2 : ℤ) (4 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)).trans (congrArg M.number (by norm_num))) (9 : ℂ)
            have _indices : Finset.Icc (2 : ℤ) (4 : ℤ) = {(2 : ℤ), (3 : ℤ), (4 : ℤ)} := by decide
            norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num : (9 : ℂ) = (9 : ℂ)))).symm)))
        )
    )
  let _object_w12 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
  let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
    intro _raw_i2 h_126 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_126)
    have h_126 : Litex.In _value_i2 (Litex.Z (M := M)) := h_126
    change Litex.In _value_i2 (Litex.Z (M := M))
    exact h_126));
  (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))

  have h_1 : (by
    let _equal_wd_1_0 := _object_w12
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (let _equal_wd_1_0 := _object_w12;
          (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) ((show (Litex.denote _equal_wd_1_0) = M.number (9 : ℂ) from (by
            let _aggregate := _equal_wd_1_0
            have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
              let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
              intro _raw_i2 h_153 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_153)
              have h_153 : Litex.In _value_i2 (Litex.Z (M := M)) := h_153
              change Litex.In _value_i2 (Litex.Z (M := M))
              exact h_153));
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
            have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
              let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
              intro _raw_i2 h_173 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_173)
              have h_173 : Litex.In _value_i2 (Litex.Z (M := M)) := h_173
              change Litex.In _value_i2 (Litex.Z (M := M))
              exact h_173));
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
            have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (4 : ℂ))) = (4 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
              let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
              intro _raw_i2 h_193 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_193)
              have h_193 : Litex.In _value_i2 (Litex.Z (M := M)) := h_193
              change Litex.In _value_i2 (Litex.Z (M := M))
              exact h_193));
            let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
            (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) True.intro))
              let _literal := (_equal_wd_1_0).val.function
              have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
              have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
              have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
              have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (4 : ℂ)) := rfl
              have _calculated : (M.number (4 : ℂ)) = M.number (4 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              have _argument : Litex.denote _call.val.argument = M.number (4 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))
              exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (4 : ℂ))
            apply Litex.rangeAggregateDenote _aggregate (2 : ℤ) (4 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)).trans (congrArg M.number (by norm_num))) (9 : ℂ)
            have _indices : Finset.Icc (2 : ℤ) (4 : ℤ) = {(2 : ℤ), (3 : ℤ), (4 : ℤ)} := by decide
            norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num : (9 : ℂ) = (9 : ℂ)))).symm)))
        )
    )
  exact True.intro
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_aggregates_x2f_statement_x2e_lit
