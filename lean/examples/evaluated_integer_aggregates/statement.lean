import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_integer_x5f_aggregates_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_201 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
  let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i1 (M.number (3 : ℂ)))) (by
    intro _raw_i1 h_215 _
    let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_215)
    have h_215 : Litex.In _value_i1 (Litex.Z (M := M)) := h_215
    change (by
      let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_215 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_215 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      exact (Litex.modInZ _atomic_wd_1_0))));
  (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i1 (M.number (3 : ℂ)))) (by
          intro _raw_i1 h_215 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_215)
          have h_215 : Litex.In _value_i1 (Litex.Z (M := M)) := h_215
          change (by
            let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_215 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_215 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.modInZ _atomic_wd_1_0))));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) (((Eq.refl (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i1 (M.number (3 : ℂ)))) (by
          intro _raw_i1 h_14 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
          have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
          change (by
            let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_14 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_14 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.modInZ _atomic_wd_1_0))));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))))).trans (show (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i1 (M.number (3 : ℂ)))) (by
          intro _raw_i1 h_14 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
          have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
          change (by
            let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_14 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_14 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.modInZ _atomic_wd_1_0))));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))) = M.number (4 : ℂ) from (by
          let _aggregate := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i1 (M.number (3 : ℂ)))) (by
            intro _raw_i1 h_14 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
            have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
            change (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_14 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_14 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.modInZ _atomic_wd_1_0))));
          (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (1 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i1 (M.number (3 : ℂ)))) (by
            intro _raw_i1 h_58 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_58)
            have h_58 : Litex.In _value_i1 (Litex.Z (M := M)) := h_58
            change (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_58 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_58 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.modInZ _atomic_wd_1_0))));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i1 (M.number (3 : ℂ)))) (by
            intro _raw_i1 h_58 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_58)
            have h_58 : Litex.In _value_i1 (Litex.Z (M := M)) := h_58
            change (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_58 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_58 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.modInZ _atomic_wd_1_0))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = ((Litex.integerDivisionValue (M := M) false) (M.number (1 : ℂ)) (M.number (3 : ℂ))) := rfl
            have _calculated : ((Litex.integerDivisionValue (M := M) false) (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number (1 : ℂ) := (show ((Litex.integerDivisionValue (M := M) false) (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number (1 : ℂ) from (congrArg₂ (Litex.integerDivisionValue (M := M) false) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
            have _numeric := Litex.integerDivisionValue_numbers false (M := M) (1 : ℤ) (3 : ℤ)
            norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
            exact _numeric))
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i1 (M.number (3 : ℂ)))) (by
            intro _raw_i1 h_97 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_97)
            have h_97 : Litex.In _value_i1 (Litex.Z (M := M)) := h_97
            change (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_97 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_97 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.modInZ _atomic_wd_1_0))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i1 (M.number (3 : ℂ)))) (by
            intro _raw_i1 h_97 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_97)
            have h_97 : Litex.In _value_i1 (Litex.Z (M := M)) := h_97
            change (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_97 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_97 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.modInZ _atomic_wd_1_0))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = ((Litex.integerDivisionValue (M := M) false) (M.number (2 : ℂ)) (M.number (3 : ℂ))) := rfl
            have _calculated : ((Litex.integerDivisionValue (M := M) false) (M.number (2 : ℂ)) (M.number (3 : ℂ))) = M.number (2 : ℂ) := (show ((Litex.integerDivisionValue (M := M) false) (M.number (2 : ℂ)) (M.number (3 : ℂ))) = M.number (2 : ℂ) from (congrArg₂ (Litex.integerDivisionValue (M := M) false) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
            have _numeric := Litex.integerDivisionValue_numbers false (M := M) (2 : ℤ) (3 : ℤ)
            norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
            exact _numeric))
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (0 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i1 (M.number (3 : ℂ)))) (by
            intro _raw_i1 h_136 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_136)
            have h_136 : Litex.In _value_i1 (Litex.Z (M := M)) := h_136
            change (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_136 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_136 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.modInZ _atomic_wd_1_0))));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i1 (M.number (3 : ℂ)))) (by
            intro _raw_i1 h_136 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_136)
            have h_136 : Litex.In _value_i1 (Litex.Z (M := M)) := h_136
            change (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_136 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_136 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.modInZ _atomic_wd_1_0))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = ((Litex.integerDivisionValue (M := M) false) (M.number (3 : ℂ)) (M.number (3 : ℂ))) := rfl
            have _calculated : ((Litex.integerDivisionValue (M := M) false) (M.number (3 : ℂ)) (M.number (3 : ℂ))) = M.number (0 : ℂ) := (show ((Litex.integerDivisionValue (M := M) false) (M.number (3 : ℂ)) (M.number (3 : ℂ))) = M.number (0 : ℂ) from (congrArg₂ (Litex.integerDivisionValue (M := M) false) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
            have _numeric := Litex.integerDivisionValue_numbers false (M := M) (3 : ℤ) (3 : ℤ)
            norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
            exact _numeric))
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (0 : ℂ))
          have _aggregate_term_3 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (4 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i1 (M.number (3 : ℂ)))) (by
            intro _raw_i1 h_175 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_175)
            have h_175 : Litex.In _value_i1 (Litex.Z (M := M)) := h_175
            change (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_175 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_175 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.modInZ _atomic_wd_1_0))));
          let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i1 (M.number (3 : ℂ)))) (by
            intro _raw_i1 h_175 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_175)
            have h_175 : Litex.In _value_i1 (Litex.Z (M := M)) := h_175
            change (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_175 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mod _value_i1 (Litex.number (M := M) (3 : ℂ)) h_175 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.modInZ _atomic_wd_1_0))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = ((Litex.integerDivisionValue (M := M) false) (M.number (4 : ℂ)) (M.number (3 : ℂ))) := rfl
            have _calculated : ((Litex.integerDivisionValue (M := M) false) (M.number (4 : ℂ)) (M.number (3 : ℂ))) = M.number (1 : ℂ) := (show ((Litex.integerDivisionValue (M := M) false) (M.number (4 : ℂ)) (M.number (3 : ℂ))) = M.number (1 : ℂ) from (congrArg₂ (Litex.integerDivisionValue (M := M) false) (show (M.number (4 : ℂ)) = M.number (4 : ℂ) from (congrArg M.number (show (4 : ℂ) = (4 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
            have _numeric := Litex.integerDivisionValue_numbers false (M := M) (4 : ℤ) (3 : ℤ)
            norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
            exact _numeric))
            have _argument : Litex.denote _call.val.argument = M.number (4 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          apply Litex.rangeAggregateDenote _aggregate (1 : ℤ) (4 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)).trans (congrArg M.number (by norm_num))) (4 : ℂ)
          have _indices : Finset.Icc (1 : ℤ) (4 : ℤ) = {(1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2, _aggregate_term_3]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))).symm)))
      )
  )

noncomputable def _object_w14 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i2 (M.number (3 : ℂ)))) (by
  intro _raw_i2 h_260 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_260)
  have h_260 : Litex.In _value_i2 (Litex.Z (M := M)) := h_260
  change (by
    let _atomic_wd_1_0 := (Litex.mod _value_i2 (Litex.number (M := M) (3 : ℂ)) h_260 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.mod _value_i2 (Litex.number (M := M) (3 : ℂ)) h_260 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact (Litex.modInZ _atomic_wd_1_0))));
(Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) = (4 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))

theorem h_246 : (by
  let _equal_wd_1_0 := (_object_w14 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w14 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) ((show (Litex.denote _equal_wd_1_0) = M.number (4 : ℂ) from (by
          let _aggregate := _equal_wd_1_0
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (1 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i2 (M.number (3 : ℂ)))) (by
            intro _raw_i2 h_306 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_306)
            have h_306 : Litex.In _value_i2 (Litex.Z (M := M)) := h_306
            change (by
              let _atomic_wd_1_0 := (Litex.mod _value_i2 (Litex.number (M := M) (3 : ℂ)) h_306 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mod _value_i2 (Litex.number (M := M) (3 : ℂ)) h_306 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.modInZ _atomic_wd_1_0))));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = ((Litex.integerDivisionValue (M := M) false) (M.number (1 : ℂ)) (M.number (3 : ℂ))) := rfl
            have _calculated : ((Litex.integerDivisionValue (M := M) false) (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number (1 : ℂ) := (show ((Litex.integerDivisionValue (M := M) false) (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number (1 : ℂ) from (congrArg₂ (Litex.integerDivisionValue (M := M) false) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
            have _numeric := Litex.integerDivisionValue_numbers false (M := M) (1 : ℤ) (3 : ℤ)
            norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
            exact _numeric))
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i2 (M.number (3 : ℂ)))) (by
            intro _raw_i2 h_345 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_345)
            have h_345 : Litex.In _value_i2 (Litex.Z (M := M)) := h_345
            change (by
              let _atomic_wd_1_0 := (Litex.mod _value_i2 (Litex.number (M := M) (3 : ℂ)) h_345 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mod _value_i2 (Litex.number (M := M) (3 : ℂ)) h_345 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.modInZ _atomic_wd_1_0))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = ((Litex.integerDivisionValue (M := M) false) (M.number (2 : ℂ)) (M.number (3 : ℂ))) := rfl
            have _calculated : ((Litex.integerDivisionValue (M := M) false) (M.number (2 : ℂ)) (M.number (3 : ℂ))) = M.number (2 : ℂ) := (show ((Litex.integerDivisionValue (M := M) false) (M.number (2 : ℂ)) (M.number (3 : ℂ))) = M.number (2 : ℂ) from (congrArg₂ (Litex.integerDivisionValue (M := M) false) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
            have _numeric := Litex.integerDivisionValue_numbers false (M := M) (2 : ℤ) (3 : ℤ)
            norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
            exact _numeric))
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (0 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i2 (M.number (3 : ℂ)))) (by
            intro _raw_i2 h_384 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_384)
            have h_384 : Litex.In _value_i2 (Litex.Z (M := M)) := h_384
            change (by
              let _atomic_wd_1_0 := (Litex.mod _value_i2 (Litex.number (M := M) (3 : ℂ)) h_384 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mod _value_i2 (Litex.number (M := M) (3 : ℂ)) h_384 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.modInZ _atomic_wd_1_0))));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = ((Litex.integerDivisionValue (M := M) false) (M.number (3 : ℂ)) (M.number (3 : ℂ))) := rfl
            have _calculated : ((Litex.integerDivisionValue (M := M) false) (M.number (3 : ℂ)) (M.number (3 : ℂ))) = M.number (0 : ℂ) := (show ((Litex.integerDivisionValue (M := M) false) (M.number (3 : ℂ)) (M.number (3 : ℂ))) = M.number (0 : ℂ) from (congrArg₂ (Litex.integerDivisionValue (M := M) false) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
            have _numeric := Litex.integerDivisionValue_numbers false (M := M) (3 : ℤ) (3 : ℤ)
            norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
            exact _numeric))
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (0 : ℂ))
          have _aggregate_term_3 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (4 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i2 (M.number (3 : ℂ)))) (by
            intro _raw_i2 h_423 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_423)
            have h_423 : Litex.In _value_i2 (Litex.Z (M := M)) := h_423
            change (by
              let _atomic_wd_1_0 := (Litex.mod _value_i2 (Litex.number (M := M) (3 : ℂ)) h_423 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mod _value_i2 (Litex.number (M := M) (3 : ℂ)) h_423 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.modInZ _atomic_wd_1_0))));
          let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = ((Litex.integerDivisionValue (M := M) false) (M.number (4 : ℂ)) (M.number (3 : ℂ))) := rfl
            have _calculated : ((Litex.integerDivisionValue (M := M) false) (M.number (4 : ℂ)) (M.number (3 : ℂ))) = M.number (1 : ℂ) := (show ((Litex.integerDivisionValue (M := M) false) (M.number (4 : ℂ)) (M.number (3 : ℂ))) = M.number (1 : ℂ) from (congrArg₂ (Litex.integerDivisionValue (M := M) false) (show (M.number (4 : ℂ)) = M.number (4 : ℂ) from (congrArg M.number (show (4 : ℂ) = (4 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
            have _numeric := Litex.integerDivisionValue_numbers false (M := M) (4 : ℤ) (3 : ℤ)
            norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
            exact _numeric))
            have _argument : Litex.denote _call.val.argument = M.number (4 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          apply Litex.rangeAggregateDenote _aggregate (1 : ℤ) (4 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)).trans (congrArg M.number (by norm_num))) (4 : ℂ)
          have _indices : Finset.Icc (1 : ℤ) (4 : ℤ) = {(1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2, _aggregate_term_3]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))).symm)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_integer_x5f_aggregates_x2f_statement_x2e_lit
