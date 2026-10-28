import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_square_x5f_root_x5f_aggregates_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4611 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
  let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i1 _raw_i1))) (by
    intro _raw_i1 h_4625 _
    let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_4625)
    have h_4625 : Litex.In _value_i1 (Litex.Z (M := M)) := h_4625
    change (by
      let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_4625) (Litex.integerToComplex _value_i1 h_4625));
      (Litex.sqrt _wd_2_0 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_4625) (Litex.integerToReal _value_i1 h_4625))) (by
        let _atomic_wd_2_1 := _wd_2_0
        exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_4625)))))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_4625) (Litex.integerToComplex _value_i1 h_4625));
      (Litex.sqrt _wd_2_0 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_4625) (Litex.integerToReal _value_i1 h_4625))) (by
        let _atomic_wd_2_1 := _wd_2_0
        exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_4625)))))
      exact (by
        let _litex_sqrt := _atomic_wd_1_0
        exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
      ))));
  (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i1 _raw_i1))) (by
          intro _raw_i1 h_4625 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_4625)
          have h_4625 : Litex.In _value_i1 (Litex.Z (M := M)) := h_4625
          change (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_4625) (Litex.integerToComplex _value_i1 h_4625));
            (Litex.sqrt _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_4625) (Litex.integerToReal _value_i1 h_4625))) (by
              let _atomic_wd_2_1 := _wd_2_0
              exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_4625)))))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
          exact (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_4625) (Litex.integerToComplex _value_i1 h_4625));
            (Litex.sqrt _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_4625) (Litex.integerToReal _value_i1 h_4625))) (by
              let _atomic_wd_2_1 := _wd_2_0
              exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_4625)))))
            exact (by
              let _litex_sqrt := _atomic_wd_1_0
              exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
            ))));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) (((Eq.refl (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i1 _raw_i1))) (by
          intro _raw_i1 h_14 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
          have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
          change (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_14) (Litex.integerToComplex _value_i1 h_14));
            (Litex.sqrt _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_14) (Litex.integerToReal _value_i1 h_14))) (by
              let _atomic_wd_2_1 := _wd_2_0
              exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_14)))))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
          exact (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_14) (Litex.integerToComplex _value_i1 h_14));
            (Litex.sqrt _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_14) (Litex.integerToReal _value_i1 h_14))) (by
              let _atomic_wd_2_1 := _wd_2_0
              exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_14)))))
            exact (by
              let _litex_sqrt := _atomic_wd_1_0
              exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
            ))));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))))).trans (show (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i1 _raw_i1))) (by
          intro _raw_i1 h_14 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
          have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
          change (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_14) (Litex.integerToComplex _value_i1 h_14));
            (Litex.sqrt _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_14) (Litex.integerToReal _value_i1 h_14))) (by
              let _atomic_wd_2_1 := _wd_2_0
              exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_14)))))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
          exact (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_14) (Litex.integerToComplex _value_i1 h_14));
            (Litex.sqrt _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_14) (Litex.integerToReal _value_i1 h_14))) (by
              let _atomic_wd_2_1 := _wd_2_0
              exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_14)))))
            exact (by
              let _litex_sqrt := _atomic_wd_1_0
              exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
            ))));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))) = M.number (6 : ℂ) from (by
          let _aggregate := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i1 _raw_i1))) (by
            intro _raw_i1 h_14 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
            have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
            change (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_14) (Litex.integerToComplex _value_i1 h_14));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_14) (Litex.integerToReal _value_i1 h_14))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_14)))))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_14) (Litex.integerToComplex _value_i1 h_14));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_14) (Litex.integerToReal _value_i1 h_14))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_14)))))
              exact (by
                let _litex_sqrt := _atomic_wd_1_0
                exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
              ))));
          (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (1 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i1 _raw_i1))) (by
            intro _raw_i1 h_1171 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_1171)
            have h_1171 : Litex.In _value_i1 (Litex.Z (M := M)) := h_1171
            change (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_1171) (Litex.integerToComplex _value_i1 h_1171));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_1171) (Litex.integerToReal _value_i1 h_1171))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_1171)))))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_1171) (Litex.integerToComplex _value_i1 h_1171));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_1171) (Litex.integerToReal _value_i1 h_1171))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_1171)))))
              exact (by
                let _litex_sqrt := _atomic_wd_1_0
                exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
              ))));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i1 _raw_i1))) (by
            intro _raw_i1 h_1171 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_1171)
            have h_1171 : Litex.In _value_i1 (Litex.Z (M := M)) := h_1171
            change (by
              let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_1171) (Litex.integerToComplex _value_i1 h_1171));
              (Litex.sqrt _wd_1_0 (by
                let _atomic_wd_2_0 := _wd_1_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_1171) (Litex.integerToReal _value_i1 h_1171))) (by
                let _atomic_wd_2_1 := _wd_1_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_1171)))))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_1171) (Litex.integerToComplex _value_i1 h_1171));
              (Litex.sqrt _wd_1_0 (by
                let _atomic_wd_2_0 := _wd_1_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_1171) (Litex.integerToReal _value_i1 h_1171))) (by
                let _atomic_wd_2_1 := _wd_1_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_1171)))))
              exact (by
                let _litex_sqrt := _atomic_wd_1_0
                exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
              ))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (Litex.sqrtValue (M := M) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) := rfl
            have _calculated : (Litex.sqrtValue (M := M) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = M.number (1 : ℂ) := (show (Litex.sqrtValue (M := M) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = M.number (1 : ℂ) from (congrArg (Litex.sqrtValue (M := M)) (show (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = M.number (1 : ℂ) from ((congrArg₂ M.mulValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.mul_numbers (1 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (by
            have _argument : (1 : ℂ) = (((1 : ℝ) : ℝ) : ℂ) := by norm_num
            have _root : Real.sqrt (1 : ℝ) = (1 : ℝ) := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
            have _cast : (((1 : ℝ) : ℝ) : ℂ) = (1 : ℂ) := by norm_num
            exact (congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) _argument).trans ((Litex.sqrtValue_number (M := M) (1 : ℝ)).trans (congrArg M.number ((congrArg (fun x : ℝ => (x : ℂ)) _root).trans _cast)))))
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i1 _raw_i1))) (by
            intro _raw_i1 h_2322 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_2322)
            have h_2322 : Litex.In _value_i1 (Litex.Z (M := M)) := h_2322
            change (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_2322) (Litex.integerToComplex _value_i1 h_2322));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_2322) (Litex.integerToReal _value_i1 h_2322))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_2322)))))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_2322) (Litex.integerToComplex _value_i1 h_2322));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_2322) (Litex.integerToReal _value_i1 h_2322))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_2322)))))
              exact (by
                let _litex_sqrt := _atomic_wd_1_0
                exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
              ))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i1 _raw_i1))) (by
            intro _raw_i1 h_2322 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_2322)
            have h_2322 : Litex.In _value_i1 (Litex.Z (M := M)) := h_2322
            change (by
              let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_2322) (Litex.integerToComplex _value_i1 h_2322));
              (Litex.sqrt _wd_1_0 (by
                let _atomic_wd_2_0 := _wd_1_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_2322) (Litex.integerToReal _value_i1 h_2322))) (by
                let _atomic_wd_2_1 := _wd_1_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_2322)))))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_2322) (Litex.integerToComplex _value_i1 h_2322));
              (Litex.sqrt _wd_1_0 (by
                let _atomic_wd_2_0 := _wd_1_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_2322) (Litex.integerToReal _value_i1 h_2322))) (by
                let _atomic_wd_2_1 := _wd_1_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_2322)))))
              exact (by
                let _litex_sqrt := _atomic_wd_1_0
                exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
              ))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (Litex.sqrtValue (M := M) (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ)))) := rfl
            have _calculated : (Litex.sqrtValue (M := M) (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ)))) = M.number (2 : ℂ) := (show (Litex.sqrtValue (M := M) (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ)))) = M.number (2 : ℂ) from (congrArg (Litex.sqrtValue (M := M)) (show (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) = M.number (4 : ℂ) from ((congrArg₂ M.mulValue (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((M.mul_numbers (2 : ℂ) (2 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (by
            have _argument : (4 : ℂ) = (((4 : ℝ) : ℝ) : ℂ) := by norm_num
            have _root : Real.sqrt (4 : ℝ) = (2 : ℝ) := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
            have _cast : (((2 : ℝ) : ℝ) : ℂ) = (2 : ℂ) := by norm_num
            exact (congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) _argument).trans ((Litex.sqrtValue_number (M := M) (4 : ℝ)).trans (congrArg M.number ((congrArg (fun x : ℝ => (x : ℂ)) _root).trans _cast)))))
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i1 _raw_i1))) (by
            intro _raw_i1 h_3473 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_3473)
            have h_3473 : Litex.In _value_i1 (Litex.Z (M := M)) := h_3473
            change (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_3473) (Litex.integerToComplex _value_i1 h_3473));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_3473) (Litex.integerToReal _value_i1 h_3473))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_3473)))))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_3473) (Litex.integerToComplex _value_i1 h_3473));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_3473) (Litex.integerToReal _value_i1 h_3473))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_3473)))))
              exact (by
                let _litex_sqrt := _atomic_wd_1_0
                exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
              ))));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i1 _raw_i1))) (by
            intro _raw_i1 h_3473 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_3473)
            have h_3473 : Litex.In _value_i1 (Litex.Z (M := M)) := h_3473
            change (by
              let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_3473) (Litex.integerToComplex _value_i1 h_3473));
              (Litex.sqrt _wd_1_0 (by
                let _atomic_wd_2_0 := _wd_1_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_3473) (Litex.integerToReal _value_i1 h_3473))) (by
                let _atomic_wd_2_1 := _wd_1_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_3473)))))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i1 (Litex.integerToComplex _value_i1 h_3473) (Litex.integerToComplex _value_i1 h_3473));
              (Litex.sqrt _wd_1_0 (by
                let _atomic_wd_2_0 := _wd_1_0
                exact (Litex.mulInR _value_i1 _value_i1 (Litex.integerToReal _value_i1 h_3473) (Litex.integerToReal _value_i1 h_3473))) (by
                let _atomic_wd_2_1 := _wd_1_0
                exact (Litex.mulSelfNonnegative _value_i1 (Litex.integerToReal _value_i1 h_3473)))))
              exact (by
                let _litex_sqrt := _atomic_wd_1_0
                exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
              ))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (Litex.sqrtValue (M := M) (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ)))) := rfl
            have _calculated : (Litex.sqrtValue (M := M) (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ)))) = M.number (3 : ℂ) := (show (Litex.sqrtValue (M := M) (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ)))) = M.number (3 : ℂ) from (congrArg (Litex.sqrtValue (M := M)) (show (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) = M.number (9 : ℂ) from ((congrArg₂ M.mulValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.mul_numbers (3 : ℂ) (3 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (by
            have _argument : (9 : ℂ) = (((9 : ℝ) : ℝ) : ℂ) := by norm_num
            have _root : Real.sqrt (9 : ℝ) = (3 : ℝ) := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
            have _cast : (((3 : ℝ) : ℝ) : ℂ) = (3 : ℂ) := by norm_num
            exact (congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) _argument).trans ((Litex.sqrtValue_number (M := M) (9 : ℝ)).trans (congrArg M.number ((congrArg (fun x : ℝ => (x : ℂ)) _root).trans _cast)))))
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
          apply Litex.rangeAggregateDenote _aggregate (1 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (6 : ℂ)
          have _indices : Finset.Icc (1 : ℤ) (3 : ℤ) = {(1 : ℤ), (2 : ℤ), (3 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = (6 : ℂ)))).symm)))
      )
  )

noncomputable def _object_w12 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i2 _raw_i2))) (by
  intro _raw_i2 h_5783 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5783)
  have h_5783 : Litex.In _value_i2 (Litex.Z (M := M)) := h_5783
  change (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_5783) (Litex.integerToComplex _value_i2 h_5783));
    (Litex.sqrt _wd_2_0 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.mulInR _value_i2 _value_i2 (Litex.integerToReal _value_i2 h_5783) (Litex.integerToReal _value_i2 h_5783))) (by
      let _atomic_wd_2_1 := _wd_2_0
      exact (Litex.mulSelfNonnegative _value_i2 (Litex.integerToReal _value_i2 h_5783)))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_5783) (Litex.integerToComplex _value_i2 h_5783));
    (Litex.sqrt _wd_2_0 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.mulInR _value_i2 _value_i2 (Litex.integerToReal _value_i2 h_5783) (Litex.integerToReal _value_i2 h_5783))) (by
      let _atomic_wd_2_1 := _wd_2_0
      exact (Litex.mulSelfNonnegative _value_i2 (Litex.integerToReal _value_i2 h_5783)))))
    exact (by
      let _litex_sqrt := _atomic_wd_1_0
      exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
    ))));
(Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))

theorem h_5769 : (by
  let _equal_wd_1_0 := (_object_w12 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w12 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) ((show (Litex.denote _equal_wd_1_0) = M.number (6 : ℂ) from (by
          let _aggregate := _equal_wd_1_0
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (1 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i2 _raw_i2))) (by
            intro _raw_i2 h_6942 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6942)
            have h_6942 : Litex.In _value_i2 (Litex.Z (M := M)) := h_6942
            change (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_6942) (Litex.integerToComplex _value_i2 h_6942));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i2 _value_i2 (Litex.integerToReal _value_i2 h_6942) (Litex.integerToReal _value_i2 h_6942))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i2 (Litex.integerToReal _value_i2 h_6942)))))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_6942) (Litex.integerToComplex _value_i2 h_6942));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i2 _value_i2 (Litex.integerToReal _value_i2 h_6942) (Litex.integerToReal _value_i2 h_6942))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i2 (Litex.integerToReal _value_i2 h_6942)))))
              exact (by
                let _litex_sqrt := _atomic_wd_1_0
                exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
              ))));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (Litex.sqrtValue (M := M) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) := rfl
            have _calculated : (Litex.sqrtValue (M := M) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = M.number (1 : ℂ) := (show (Litex.sqrtValue (M := M) (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = M.number (1 : ℂ) from (congrArg (Litex.sqrtValue (M := M)) (show (M.mulValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = M.number (1 : ℂ) from ((congrArg₂ M.mulValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.mul_numbers (1 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (by
            have _argument : (1 : ℂ) = (((1 : ℝ) : ℝ) : ℂ) := by norm_num
            have _root : Real.sqrt (1 : ℝ) = (1 : ℝ) := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
            have _cast : (((1 : ℝ) : ℝ) : ℂ) = (1 : ℂ) := by norm_num
            exact (congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) _argument).trans ((Litex.sqrtValue_number (M := M) (1 : ℝ)).trans (congrArg M.number ((congrArg (fun x : ℝ => (x : ℂ)) _root).trans _cast)))))
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i2 _raw_i2))) (by
            intro _raw_i2 h_8093 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_8093)
            have h_8093 : Litex.In _value_i2 (Litex.Z (M := M)) := h_8093
            change (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_8093) (Litex.integerToComplex _value_i2 h_8093));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i2 _value_i2 (Litex.integerToReal _value_i2 h_8093) (Litex.integerToReal _value_i2 h_8093))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i2 (Litex.integerToReal _value_i2 h_8093)))))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_8093) (Litex.integerToComplex _value_i2 h_8093));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i2 _value_i2 (Litex.integerToReal _value_i2 h_8093) (Litex.integerToReal _value_i2 h_8093))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i2 (Litex.integerToReal _value_i2 h_8093)))))
              exact (by
                let _litex_sqrt := _atomic_wd_1_0
                exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
              ))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (Litex.sqrtValue (M := M) (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ)))) := rfl
            have _calculated : (Litex.sqrtValue (M := M) (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ)))) = M.number (2 : ℂ) := (show (Litex.sqrtValue (M := M) (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ)))) = M.number (2 : ℂ) from (congrArg (Litex.sqrtValue (M := M)) (show (M.mulValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) = M.number (4 : ℂ) from ((congrArg₂ M.mulValue (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((M.mul_numbers (2 : ℂ) (2 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (by
            have _argument : (4 : ℂ) = (((4 : ℝ) : ℝ) : ℂ) := by norm_num
            have _root : Real.sqrt (4 : ℝ) = (2 : ℝ) := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
            have _cast : (((2 : ℝ) : ℝ) : ℂ) = (2 : ℂ) := by norm_num
            exact (congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) _argument).trans ((Litex.sqrtValue_number (M := M) (4 : ℝ)).trans (congrArg M.number ((congrArg (fun x : ℝ => (x : ℂ)) _root).trans _cast)))))
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.sqrtValue (M := M) (M.mulValue _raw_i2 _raw_i2))) (by
            intro _raw_i2 h_9244 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_9244)
            have h_9244 : Litex.In _value_i2 (Litex.Z (M := M)) := h_9244
            change (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_9244) (Litex.integerToComplex _value_i2 h_9244));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i2 _value_i2 (Litex.integerToReal _value_i2 h_9244) (Litex.integerToReal _value_i2 h_9244))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i2 (Litex.integerToReal _value_i2 h_9244)))))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.mul _value_i2 _value_i2 (Litex.integerToComplex _value_i2 h_9244) (Litex.integerToComplex _value_i2 h_9244));
              (Litex.sqrt _wd_2_0 (by
                let _atomic_wd_2_0 := _wd_2_0
                exact (Litex.mulInR _value_i2 _value_i2 (Litex.integerToReal _value_i2 h_9244) (Litex.integerToReal _value_i2 h_9244))) (by
                let _atomic_wd_2_1 := _wd_2_0
                exact (Litex.mulSelfNonnegative _value_i2 (Litex.integerToReal _value_i2 h_9244)))))
              exact (by
                let _litex_sqrt := _atomic_wd_1_0
                exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2
              ))));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (Litex.sqrtValue (M := M) (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ)))) := rfl
            have _calculated : (Litex.sqrtValue (M := M) (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ)))) = M.number (3 : ℂ) := (show (Litex.sqrtValue (M := M) (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ)))) = M.number (3 : ℂ) from (congrArg (Litex.sqrtValue (M := M)) (show (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) = M.number (9 : ℂ) from ((congrArg₂ M.mulValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.mul_numbers (3 : ℂ) (3 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (by
            have _argument : (9 : ℂ) = (((9 : ℝ) : ℝ) : ℂ) := by norm_num
            have _root : Real.sqrt (9 : ℝ) = (3 : ℝ) := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
            have _cast : (((3 : ℝ) : ℝ) : ℂ) = (3 : ℂ) := by norm_num
            exact (congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) _argument).trans ((Litex.sqrtValue_number (M := M) (9 : ℝ)).trans (congrArg M.number ((congrArg (fun x : ℝ => (x : ℂ)) _root).trans _cast)))))
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
          apply Litex.rangeAggregateDenote _aggregate (1 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (6 : ℂ)
          have _indices : Finset.Icc (1 : ℤ) (3 : ℤ) = {(1 : ℤ), (2 : ℤ), (3 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = (6 : ℂ)))).symm)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_square_x5f_root_x5f_aggregates_x2f_statement_x2e_lit
