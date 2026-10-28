import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_real_x5f_aggregates_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_140 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
  let _wd_2_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
    intro _raw_i1 h_154 _
    let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_154)
    have h_154 : Litex.In _value_i1 (Litex.Z (M := M)) := h_154
    change Litex.In _value_i1 (Litex.Z (M := M))
    exact h_154));
  (Litex.rangeAggregate false _wd_2_0 _wd_2_1 _wd_2_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_2_0 _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal _wd_2_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_2_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_2_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)));
  let _wd_1_1 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (Litex.floor _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((7 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((7 : ℂ) / (2 : ℂ)) ((7 : ℝ) / (2 : ℝ)) (by norm_num))))));
  (Litex.max _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
    let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
    let _wd_2_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
      intro _raw_i1 h_187 _
      let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_187)
      have h_187 : Litex.In _value_i1 (Litex.Z (M := M)) := h_187
      change Litex.In _value_i1 (Litex.Z (M := M))
      exact h_187));
    (Litex.rangeAggregate false _wd_2_0 _wd_2_1 _wd_2_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_2_0 _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal _wd_2_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_2_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_2_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
    exact (Litex.integerToReal _atomic_wd_1_0 (Litex.rangeAggregateMember _atomic_wd_1_0 .integer rfl))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (3 : ℂ) (Litex.R (M := M)) (let _round := _atomic_wd_1_0;
    let _member : Litex.In _round Litex.C := Litex.integerToComplex _round (Litex.roundingInZ _round);
    (Litex.roundingDenoteReal _round ((7 : ℝ) / (2 : ℝ)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.arg).wd.1 ((_atomic_wd_1_0).val.arg).wd.2.1 ((_atomic_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((7 : ℂ) / (2 : ℂ)) = ((((7 : ℝ) / (2 : ℝ)) : ℝ) : ℂ))))).trans (congrArg M.number (by have _value : Int.floor ((7 : ℝ) / (2 : ℝ)) = (3 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩; change ((Int.floor ((7 : ℝ) / (2 : ℝ)) : ℤ) : ℂ) = (3 : ℂ); rw [_value]; norm_num))) (Litex.NativeBridge.numberInROfEq (3 : ℂ) (3 : ℝ) (by norm_num))))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_2_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_154 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_154)
          have h_154 : Litex.In _value_i1 (Litex.Z (M := M)) := h_154
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_154));
        (Litex.rangeAggregate false _wd_2_0 _wd_2_1 _wd_2_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_2_0 _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_2_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_2_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_2_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)));
        let _wd_1_1 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (Litex.floor _wd_2_0 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((7 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((7 : ℂ) / (2 : ℂ)) ((7 : ℝ) / (2 : ℝ)) (by norm_num))))));
        (Litex.max _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
          let _wd_2_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_187 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_187)
            have h_187 : Litex.In _value_i1 (Litex.Z (M := M)) := h_187
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_187));
          (Litex.rangeAggregate false _wd_2_0 _wd_2_1 _wd_2_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_2_0 _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _wd_2_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_2_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_2_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
          exact (Litex.integerToReal _atomic_wd_1_0 (Litex.rangeAggregateMember _atomic_wd_1_0 .integer rfl))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (3 : ℂ) (Litex.R (M := M)) (let _round := _atomic_wd_1_0;
          let _member : Litex.In _round Litex.C := Litex.integerToComplex _round (Litex.roundingInZ _round);
          (Litex.roundingDenoteReal _round ((7 : ℝ) / (2 : ℝ)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.arg).wd.1 ((_atomic_wd_1_0).val.arg).wd.2.1 ((_atomic_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((7 : ℂ) / (2 : ℂ)) = ((((7 : ℝ) / (2 : ℝ)) : ℝ) : ℂ))))).trans (congrArg M.number (by have _value : Int.floor ((7 : ℝ) / (2 : ℝ)) = (3 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩; change ((Int.floor ((7 : ℝ) / (2 : ℝ)) : ℤ) : ℂ) = (3 : ℂ); rw [_value]; norm_num))) (Litex.NativeBridge.numberInROfEq (3 : ℂ) (3 : ℝ) (by norm_num))))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = ((Litex.minMaxValue (M := M) true) (Litex.denote (_equal_wd_1_0).val.left) ((Litex.roundingValue (M := M) false) (M.divValue (M.number (7 : ℂ)) (M.number (2 : ℂ))))) from congrArg₂ (Litex.minMaxValue (M := M) true) (show Litex.denote (_equal_wd_1_0).val.left = (Litex.denote (_equal_wd_1_0).val.left) from rfl) (show Litex.denote (_equal_wd_1_0).val.right = ((Litex.roundingValue (M := M) false) (M.divValue (M.number (7 : ℂ)) (M.number (2 : ℂ)))) from congrArg (Litex.roundingValue (M := M) false) (show Litex.denote ((_equal_wd_1_0).val.right).val.arg = (M.divValue (M.number (7 : ℂ)) (M.number (2 : ℂ))) from congrArg₂ M.divValue (show Litex.denote (Litex.number (M := M) (7 : ℂ)) = (M.number (7 : ℂ)) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl)))) (((Eq.refl ((Litex.minMaxValue (M := M) true) (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_47 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_47)
          have h_47 : Litex.In _value_i1 (Litex.Z (M := M)) := h_47
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_47));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))) ((Litex.roundingValue (M := M) false) (M.divValue (M.number (7 : ℂ)) (M.number (2 : ℂ))))))).trans (show ((Litex.minMaxValue (M := M) true) (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_47 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_47)
          have h_47 : Litex.In _value_i1 (Litex.Z (M := M)) := h_47
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_47));
        (Litex.rangeAggregate false _wd_1_0 _wd_1_1 _wd_1_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_1_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))) ((Litex.roundingValue (M := M) false) (M.divValue (M.number (7 : ℂ)) (M.number (2 : ℂ))))) = M.number (6 : ℂ) from (congrArg₂ (Litex.minMaxValue (M := M) true) (show (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_47 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_47)
          have h_47 : Litex.In _value_i1 (Litex.Z (M := M)) := h_47
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_47));
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
            intro _raw_i1 h_47 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_47)
            have h_47 : Litex.In _value_i1 (Litex.Z (M := M)) := h_47
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_47));
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
            intro _raw_i1 h_93 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_93)
            have h_93 : Litex.In _value_i1 (Litex.Z (M := M)) := h_93
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_93));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_93 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_93)
            have h_93 : Litex.In _value_i1 (Litex.Z (M := M)) := h_93
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_93))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (1 : ℂ)) := rfl
            have _calculated : (M.number (1 : ℂ)) = M.number (1 : ℂ) := (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_113 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_113)
            have h_113 : Litex.In _value_i1 (Litex.Z (M := M)) := h_113
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_113));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_113 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_113)
            have h_113 : Litex.In _value_i1 (Litex.Z (M := M)) := h_113
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_113))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := rfl
            have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_133 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_133)
            have h_133 : Litex.In _value_i1 (Litex.Z (M := M)) := h_133
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_133));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_133 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_133)
            have h_133 : Litex.In _value_i1 (Litex.Z (M := M)) := h_133
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_133))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := rfl
            have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
          apply Litex.rangeAggregateDenote _aggregate (1 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (6 : ℂ)
          have _indices : Finset.Icc (1 : ℤ) (3 : ℤ) = {(1 : ℤ), (2 : ℤ), (3 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2])) (show ((Litex.roundingValue (M := M) false) (M.divValue (M.number (7 : ℂ)) (M.number (2 : ℂ)))) = M.number (3 : ℂ) from (congrArg (Litex.roundingValue (M := M) false) (show (M.divValue (M.number (7 : ℂ)) (M.number (2 : ℂ))) = M.number ((7 : ℂ) / (2 : ℂ)) from ((congrArg₂ M.divValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num))) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((M.div_numbers (7 : ℂ) (2 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))).trans (by
          have _numeric := Litex.roundingValue_number false (M := M) ((7 : ℝ) / (2 : ℝ))
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric))).trans (by
          have _numeric := Litex.minMaxValue_number true (M := M) (6 : ℝ) (3 : ℝ)
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = (6 : ℂ)))).symm)))
      )
  )

noncomputable def _object_w15 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
let _wd_2_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
  intro _raw_i2 h_234 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_234)
  have h_234 : Litex.In _value_i2 (Litex.Z (M := M)) := h_234
  change Litex.In _value_i2 (Litex.Z (M := M))
  exact h_234));
(Litex.rangeAggregate false _wd_2_0 _wd_2_1 _wd_2_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_2_0 _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal _wd_2_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_2_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_2_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)));
let _wd_1_1 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.floor _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((7 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((7 : ℂ) / (2 : ℂ)) ((7 : ℝ) / (2 : ℝ)) (by norm_num))))));
(Litex.max _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
  let _wd_2_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
    intro _raw_i2 h_267 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_267)
    have h_267 : Litex.In _value_i2 (Litex.Z (M := M)) := h_267
    change Litex.In _value_i2 (Litex.Z (M := M))
    exact h_267));
  (Litex.rangeAggregate false _wd_2_0 _wd_2_1 _wd_2_2 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal _wd_2_0 _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal _wd_2_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_2_0 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (Litex.formulaFnInFnSet _wd_2_2) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (fun k _ _ => Litex.unguardedIntegerDomain .integer _ _ (by decide) k)))
  exact (Litex.integerToReal _atomic_wd_1_0 (Litex.rangeAggregateMember _atomic_wd_1_0 .integer rfl))) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (3 : ℂ) (Litex.R (M := M)) (let _round := _atomic_wd_1_0;
  let _member : Litex.In _round Litex.C := Litex.integerToComplex _round (Litex.roundingInZ _round);
  (Litex.roundingDenoteReal _round ((7 : ℝ) / (2 : ℝ)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.arg).wd.1 ((_atomic_wd_1_0).val.arg).wd.2.1 ((_atomic_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((7 : ℂ) / (2 : ℂ)) = ((((7 : ℝ) / (2 : ℝ)) : ℝ) : ℂ))))).trans (congrArg M.number (by have _value : Int.floor ((7 : ℝ) / (2 : ℝ)) = (3 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩; change ((Int.floor ((7 : ℝ) / (2 : ℝ)) : ℤ) : ℂ) = (3 : ℂ); rw [_value]; norm_num))) (Litex.NativeBridge.numberInROfEq (3 : ℂ) (3 : ℝ) (by norm_num))))))

theorem h_220 : (by
  let _equal_wd_1_0 := (_object_w15 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w15 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = ((Litex.minMaxValue (M := M) true) (Litex.denote (_equal_wd_1_0).val.left) ((Litex.roundingValue (M := M) false) (M.divValue (M.number (7 : ℂ)) (M.number (2 : ℂ))))) from congrArg₂ (Litex.minMaxValue (M := M) true) (show Litex.denote (_equal_wd_1_0).val.left = (Litex.denote (_equal_wd_1_0).val.left) from rfl) (show Litex.denote (_equal_wd_1_0).val.right = ((Litex.roundingValue (M := M) false) (M.divValue (M.number (7 : ℂ)) (M.number (2 : ℂ)))) from congrArg (Litex.roundingValue (M := M) false) (show Litex.denote ((_equal_wd_1_0).val.right).val.arg = (M.divValue (M.number (7 : ℂ)) (M.number (2 : ℂ))) from congrArg₂ M.divValue (show Litex.denote (Litex.number (M := M) (7 : ℂ)) = (M.number (7 : ℂ)) from rfl) (show Litex.denote (Litex.number (M := M) (2 : ℂ)) = (M.number (2 : ℂ)) from rfl)))) ((show ((Litex.minMaxValue (M := M) true) (Litex.denote (_equal_wd_1_0).val.left) ((Litex.roundingValue (M := M) false) (M.divValue (M.number (7 : ℂ)) (M.number (2 : ℂ))))) = M.number (6 : ℂ) from (congrArg₂ (Litex.minMaxValue (M := M) true) (show (Litex.denote (_equal_wd_1_0).val.left) = M.number (6 : ℂ) from (by
          let _aggregate := (_equal_wd_1_0).val.left
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (1 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
            intro _raw_i2 h_315 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_315)
            have h_315 : Litex.In _value_i2 (Litex.Z (M := M)) := h_315
            change Litex.In _value_i2 (Litex.Z (M := M))
            exact h_315));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := ((_equal_wd_1_0).val.left).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (1 : ℂ)) := rfl
            have _calculated : (M.number (1 : ℂ)) = M.number (1 : ℂ) := (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
            intro _raw_i2 h_335 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_335)
            have h_335 : Litex.In _value_i2 (Litex.Z (M := M)) := h_335
            change Litex.In _value_i2 (Litex.Z (M := M))
            exact h_335));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := ((_equal_wd_1_0).val.left).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := rfl
            have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
            intro _raw_i2 h_355 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_355)
            have h_355 : Litex.In _value_i2 (Litex.Z (M := M)) := h_355
            change Litex.In _value_i2 (Litex.Z (M := M))
            exact h_355));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := ((_equal_wd_1_0).val.left).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := rfl
            have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
          apply Litex.rangeAggregateDenote _aggregate (1 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (6 : ℂ)
          have _indices : Finset.Icc (1 : ℤ) (3 : ℤ) = {(1 : ℤ), (2 : ℤ), (3 : ℤ)} := by decide
          norm_num [Litex.nativeRangeAggregate, _indices, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2])) (show ((Litex.roundingValue (M := M) false) (M.divValue (M.number (7 : ℂ)) (M.number (2 : ℂ)))) = M.number (3 : ℂ) from (congrArg (Litex.roundingValue (M := M) false) (show (M.divValue (M.number (7 : ℂ)) (M.number (2 : ℂ))) = M.number ((7 : ℂ) / (2 : ℂ)) from ((congrArg₂ M.divValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num))) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((M.div_numbers (7 : ℂ) (2 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))).trans (by
          have _numeric := Litex.roundingValue_number false (M := M) ((7 : ℝ) / (2 : ℝ))
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric))).trans (by
          have _numeric := Litex.minMaxValue_number true (M := M) (6 : ℝ) (3 : ℝ)
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = (6 : ℂ)))).symm)))
      )
  )

theorem h_971 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
  let _wd_2_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
    intro _raw_i3 h_985 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_985)
    have h_985 : Litex.In _value_i3 (Litex.Z (M := M)) := h_985
    change Litex.In _value_i3 (Litex.Z (M := M))
    exact h_985));
  let _wd_2_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
    intro _raw_i4 _raw_i5 h_1004 h_1005 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1004)
    have h_1004 : Litex.In _value_i4 (Litex.Z (M := M)) := h_1004
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1005)
    have h_1005 : Litex.In _value_i5 (Litex.Z (M := M)) := h_1005
    change (by
      let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_1004) (Litex.integerToComplex _value_i5 h_1005))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_1004) (Litex.integerToComplex _value_i5 h_1005))
      exact (Litex.subInZ _value_i4 _value_i5 h_1004 h_1005))));
  let _wd_2_4 := (Litex.number (M := M) (0 : ℂ));
  (let h_1087 : Litex.In _wd_2_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
  let h_1088 : Litex.In _wd_2_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
  let h_1089 : Litex.In _wd_2_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
  Litex.rangeFold _wd_2_0 _wd_2_1 _wd_2_2 _wd_2_3 _wd_2_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) h_1087 h_1088 (Litex.formulaFnInFnSet _wd_2_2) (Litex.formulaFnInFnSet _wd_2_3) h_1089 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i3 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
    let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
    let _wd_2_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
      intro _raw_i3 h_1106 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1106)
      have h_1106 : Litex.In _value_i3 (Litex.Z (M := M)) := h_1106
      change Litex.In _value_i3 (Litex.Z (M := M))
      exact h_1106));
    let _wd_2_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
      intro _raw_i4 _raw_i5 h_1125 h_1126 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1125)
      have h_1125 : Litex.In _value_i4 (Litex.Z (M := M)) := h_1125
      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1126)
      have h_1126 : Litex.In _value_i5 (Litex.Z (M := M)) := h_1126
      change (by
        let _atomic_wd_2_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_1125) (Litex.integerToComplex _value_i5 h_1126))
        exact Litex.In _atomic_wd_2_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_2_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_1125) (Litex.integerToComplex _value_i5 h_1126))
        exact (Litex.subInZ _value_i4 _value_i5 h_1125 h_1126))));
    let _wd_2_4 := (Litex.number (M := M) (0 : ℂ));
    (let h_1208 : Litex.In _wd_2_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
    let h_1209 : Litex.In _wd_2_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
    let h_1210 : Litex.In _wd_2_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
    Litex.rangeFold _wd_2_0 _wd_2_1 _wd_2_2 _wd_2_3 _wd_2_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) h_1208 h_1209 (Litex.formulaFnInFnSet _wd_2_2) (Litex.formulaFnInFnSet _wd_2_3) h_1210 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i3 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))
    exact (Litex.integerToReal _atomic_wd_1_0 (Litex.rangeFoldInOutput _atomic_wd_1_0)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_2_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
          intro _raw_i3 h_985 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_985)
          have h_985 : Litex.In _value_i3 (Litex.Z (M := M)) := h_985
          change Litex.In _value_i3 (Litex.Z (M := M))
          exact h_985));
        let _wd_2_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
          intro _raw_i4 _raw_i5 h_1004 h_1005 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1004)
          have h_1004 : Litex.In _value_i4 (Litex.Z (M := M)) := h_1004
          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1005)
          have h_1005 : Litex.In _value_i5 (Litex.Z (M := M)) := h_1005
          change (by
            let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_1004) (Litex.integerToComplex _value_i5 h_1005))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_1004) (Litex.integerToComplex _value_i5 h_1005))
            exact (Litex.subInZ _value_i4 _value_i5 h_1004 h_1005))));
        let _wd_2_4 := (Litex.number (M := M) (0 : ℂ));
        (let h_1087 : Litex.In _wd_2_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
        let h_1088 : Litex.In _wd_2_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
        let h_1089 : Litex.In _wd_2_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
        Litex.rangeFold _wd_2_0 _wd_2_1 _wd_2_2 _wd_2_3 _wd_2_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) h_1087 h_1088 (Litex.formulaFnInFnSet _wd_2_2) (Litex.formulaFnInFnSet _wd_2_3) h_1089 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i3 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)));
        (Litex.abs _wd_1_0 (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
          let _wd_2_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_1106 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1106)
            have h_1106 : Litex.In _value_i3 (Litex.Z (M := M)) := h_1106
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_1106));
          let _wd_2_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
            intro _raw_i4 _raw_i5 h_1125 h_1126 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1125)
            have h_1125 : Litex.In _value_i4 (Litex.Z (M := M)) := h_1125
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1126)
            have h_1126 : Litex.In _value_i5 (Litex.Z (M := M)) := h_1126
            change (by
              let _atomic_wd_2_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_1125) (Litex.integerToComplex _value_i5 h_1126))
              exact Litex.In _atomic_wd_2_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_2_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_1125) (Litex.integerToComplex _value_i5 h_1126))
              exact (Litex.subInZ _value_i4 _value_i5 h_1125 h_1126))));
          let _wd_2_4 := (Litex.number (M := M) (0 : ℂ));
          (let h_1208 : Litex.In _wd_2_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
          let h_1209 : Litex.In _wd_2_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
          let h_1210 : Litex.In _wd_2_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
          Litex.rangeFold _wd_2_0 _wd_2_1 _wd_2_2 _wd_2_3 _wd_2_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) h_1208 h_1209 (Litex.formulaFnInFnSet _wd_2_2) (Litex.formulaFnInFnSet _wd_2_3) h_1210 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i3 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))
          exact (Litex.integerToReal _atomic_wd_1_0 (Litex.rangeFoldInOutput _atomic_wd_1_0)))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.absValue (M := M) (Litex.denote (_equal_wd_1_0).val.arg)) from congrArg (Litex.absValue (M := M)) (show Litex.denote (_equal_wd_1_0).val.arg = (Litex.denote (_equal_wd_1_0).val.arg) from rfl)) (((Eq.refl (Litex.absValue (M := M) (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
          intro _raw_i3 h_496 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_496)
          have h_496 : Litex.In _value_i3 (Litex.Z (M := M)) := h_496
          change Litex.In _value_i3 (Litex.Z (M := M))
          exact h_496));
        let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
          intro _raw_i4 _raw_i5 h_515 h_516 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_515)
          have h_515 : Litex.In _value_i4 (Litex.Z (M := M)) := h_515
          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_516)
          have h_516 : Litex.In _value_i5 (Litex.Z (M := M)) := h_516
          change (by
            let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_515) (Litex.integerToComplex _value_i5 h_516))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_515) (Litex.integerToComplex _value_i5 h_516))
            exact (Litex.subInZ _value_i4 _value_i5 h_515 h_516))));
        let _wd_1_4 := (Litex.number (M := M) (0 : ℂ));
        (let h_598 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
        let h_599 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
        let h_600 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
        Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) h_598 h_599 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_600 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i3 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩))))))).trans (show (Litex.absValue (M := M) (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
          intro _raw_i3 h_496 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_496)
          have h_496 : Litex.In _value_i3 (Litex.Z (M := M)) := h_496
          change Litex.In _value_i3 (Litex.Z (M := M))
          exact h_496));
        let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
          intro _raw_i4 _raw_i5 h_515 h_516 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_515)
          have h_515 : Litex.In _value_i4 (Litex.Z (M := M)) := h_515
          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_516)
          have h_516 : Litex.In _value_i5 (Litex.Z (M := M)) := h_516
          change (by
            let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_515) (Litex.integerToComplex _value_i5 h_516))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_515) (Litex.integerToComplex _value_i5 h_516))
            exact (Litex.subInZ _value_i4 _value_i5 h_515 h_516))));
        let _wd_1_4 := (Litex.number (M := M) (0 : ℂ));
        (let h_598 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
        let h_599 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
        let h_600 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
        Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) h_598 h_599 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_600 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i3 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩))))) = M.number (6 : ℂ) from (congrArg (Litex.absValue (M := M)) (show (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
          intro _raw_i3 h_496 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_496)
          have h_496 : Litex.In _value_i3 (Litex.Z (M := M)) := h_496
          change Litex.In _value_i3 (Litex.Z (M := M))
          exact h_496));
        let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
          intro _raw_i4 _raw_i5 h_515 h_516 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_515)
          have h_515 : Litex.In _value_i4 (Litex.Z (M := M)) := h_515
          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_516)
          have h_516 : Litex.In _value_i5 (Litex.Z (M := M)) := h_516
          change (by
            let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_515) (Litex.integerToComplex _value_i5 h_516))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_515) (Litex.integerToComplex _value_i5 h_516))
            exact (Litex.subInZ _value_i4 _value_i5 h_515 h_516))));
        let _wd_1_4 := (Litex.number (M := M) (0 : ℂ));
        (let h_598 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
        let h_599 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
        let h_600 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
        Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) h_598 h_599 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_600 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i3 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))) = M.number (-6 : ℂ) from (by
          let _fold := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_496 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_496)
            have h_496 : Litex.In _value_i3 (Litex.Z (M := M)) := h_496
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_496));
          let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
            intro _raw_i4 _raw_i5 h_515 h_516 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_515)
            have h_515 : Litex.In _value_i4 (Litex.Z (M := M)) := h_515
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_516)
            have h_516 : Litex.In _value_i5 (Litex.Z (M := M)) := h_516
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_515) (Litex.integerToComplex _value_i5 h_516))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_515) (Litex.integerToComplex _value_i5 h_516))
              exact (Litex.subInZ _value_i4 _value_i5 h_515 h_516))));
          let _wd_1_4 := (Litex.number (M := M) (0 : ℂ));
          (let h_598 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
          let h_599 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
          let h_600 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
          Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) h_598 h_599 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_600 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i3 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))
          have _seed : Litex.denote _fold.val.seed = M.number (0 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))
          have _term_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (1 : ℂ)) = M.number (1 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_630 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_630)
            have h_630 : Litex.In _value_i3 (Litex.Z (M := M)) := h_630
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_630));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_630 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_630)
            have h_630 : Litex.In _value_i3 (Litex.Z (M := M)) := h_630
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_630))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (1 : ℂ)) := by change (fun (_raw_i3 : M.Value) => _raw_i3) (Litex.denote _call.val.argument) = (M.number (1 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (1 : ℂ)) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (0 : ℂ)) (M.number (1 : ℂ))) = M.number (-1 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
            intro _raw_i4 _raw_i5 h_650 h_651 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_650)
            have h_650 : Litex.In _value_i4 (Litex.Z (M := M)) := h_650
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_651)
            have h_651 : Litex.In _value_i5 (Litex.Z (M := M)) := h_651
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_650) (Litex.integerToComplex _value_i5 h_651))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_650) (Litex.integerToComplex _value_i5 h_651))
              exact (Litex.subInZ _value_i4 _value_i5 h_650 h_651))));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
            intro _raw_i4 _raw_i5 h_650 h_651 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_650)
            have h_650 : Litex.In _value_i4 (Litex.Z (M := M)) := h_650
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_651)
            have h_651 : Litex.In _value_i5 (Litex.Z (M := M)) := h_651
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_650) (Litex.integerToComplex _value_i5 h_651))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_650) (Litex.integerToComplex _value_i5 h_651))
              exact (Litex.subInZ _value_i4 _value_i5 h_650 h_651))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (0 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) := by change (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) = M.number (-1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _term_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (2 : ℂ)) = M.number (2 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_748 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_748)
            have h_748 : Litex.In _value_i3 (Litex.Z (M := M)) := h_748
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_748));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_748 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_748)
            have h_748 : Litex.In _value_i3 (Litex.Z (M := M)) := h_748
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_748))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := by change (fun (_raw_i3 : M.Value) => _raw_i3) (Litex.denote _call.val.argument) = (M.number (2 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (-1 : ℂ)) (M.number (2 : ℂ))) = M.number (-3 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
            intro _raw_i4 _raw_i5 h_768 h_769 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_768)
            have h_768 : Litex.In _value_i4 (Litex.Z (M := M)) := h_768
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_769)
            have h_769 : Litex.In _value_i5 (Litex.Z (M := M)) := h_769
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_768) (Litex.integerToComplex _value_i5 h_769))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_768) (Litex.integerToComplex _value_i5 h_769))
              exact (Litex.subInZ _value_i4 _value_i5 h_768 h_769))));
          let _wd_1_1 := (Litex.number (M := M) (-1 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-1 : ℂ) (-1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
            intro _raw_i4 _raw_i5 h_768 h_769 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_768)
            have h_768 : Litex.In _value_i4 (Litex.Z (M := M)) := h_768
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_769)
            have h_769 : Litex.In _value_i5 (Litex.Z (M := M)) := h_769
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_768) (Litex.integerToComplex _value_i5 h_769))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_768) (Litex.integerToComplex _value_i5 h_769))
              exact (Litex.subInZ _value_i4 _value_i5 h_768 h_769))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (-1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num : (-1 : ℂ) = (-1 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))) := by change (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))) = M.number (-3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _term_2 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (3 : ℂ)) = M.number (3 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_866 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_866)
            have h_866 : Litex.In _value_i3 (Litex.Z (M := M)) := h_866
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_866));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_866 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_866)
            have h_866 : Litex.In _value_i3 (Litex.Z (M := M)) := h_866
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_866))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := by change (fun (_raw_i3 : M.Value) => _raw_i3) (Litex.denote _call.val.argument) = (M.number (3 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_2 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (-3 : ℂ)) (M.number (3 : ℂ))) = M.number (-6 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
            intro _raw_i4 _raw_i5 h_886 h_887 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_886)
            have h_886 : Litex.In _value_i4 (Litex.Z (M := M)) := h_886
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_887)
            have h_887 : Litex.In _value_i5 (Litex.Z (M := M)) := h_887
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_886) (Litex.integerToComplex _value_i5 h_887))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_886) (Litex.integerToComplex _value_i5 h_887))
              exact (Litex.subInZ _value_i4 _value_i5 h_886 h_887))));
          let _wd_1_1 := (Litex.number (M := M) (-3 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-3 : ℂ) (-3 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (by
            intro _raw_i4 _raw_i5 h_886 h_887 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_886)
            have h_886 : Litex.In _value_i4 (Litex.Z (M := M)) := h_886
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_887)
            have h_887 : Litex.In _value_i5 (Litex.Z (M := M)) := h_887
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_886) (Litex.integerToComplex _value_i5 h_887))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i4 _value_i5 (Litex.integerToComplex _value_i4 h_886) (Litex.integerToComplex _value_i5 h_887))
              exact (Litex.subInZ _value_i4 _value_i5 h_886 h_887))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (-3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))) := by change (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.subValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))) = M.number (-6 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          apply Litex.rangeFoldDenote _fold (1 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (M.number (-6 : ℂ))
          have _indices : Litex.integerFoldIndices (1 : ℤ) (3 : ℤ) = [(1 : ℤ), (2 : ℤ), (3 : ℤ)] := by decide
          norm_num [Litex.foldValue, Litex.foldApply2, _indices, _seed, _term_0, _step_0, _term_1, _step_1, _term_2, _step_2]))).trans (by
          have _numeric := Litex.absValue_number (M := M) (-6 : ℝ)
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = (6 : ℂ)))).symm)))
      )
  )

noncomputable def _object_w41 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
let _wd_2_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => _raw_i6) (by
  intro _raw_i6 h_1241 _
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1241)
  have h_1241 : Litex.In _value_i6 (Litex.Z (M := M)) := h_1241
  change Litex.In _value_i6 (Litex.Z (M := M))
  exact h_1241));
let _wd_2_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.subValue _raw_i7 _raw_i8)) (by
  intro _raw_i7 _raw_i8 h_1260 h_1261 _
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1260)
  have h_1260 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1260
  let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1261)
  have h_1261 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1261
  change (by
    let _atomic_wd_1_0 := (Litex.sub _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1260) (Litex.integerToComplex _value_i8 h_1261))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sub _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1260) (Litex.integerToComplex _value_i8 h_1261))
    exact (Litex.subInZ _value_i7 _value_i8 h_1260 h_1261))));
let _wd_2_4 := (Litex.number (M := M) (0 : ℂ));
(let h_1343 : Litex.In _wd_2_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
let h_1344 : Litex.In _wd_2_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
let h_1345 : Litex.In _wd_2_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
Litex.rangeFold _wd_2_0 _wd_2_1 _wd_2_2 _wd_2_3 _wd_2_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True)) h_1343 h_1344 (Litex.formulaFnInFnSet _wd_2_2) (Litex.formulaFnInFnSet _wd_2_3) h_1345 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i6 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
  let _wd_2_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => _raw_i6) (by
    intro _raw_i6 h_1362 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1362)
    have h_1362 : Litex.In _value_i6 (Litex.Z (M := M)) := h_1362
    change Litex.In _value_i6 (Litex.Z (M := M))
    exact h_1362));
  let _wd_2_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.subValue _raw_i7 _raw_i8)) (by
    intro _raw_i7 _raw_i8 h_1381 h_1382 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1381)
    have h_1381 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1381
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1382)
    have h_1382 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1382
    change (by
      let _atomic_wd_2_0 := (Litex.sub _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1381) (Litex.integerToComplex _value_i8 h_1382))
      exact Litex.In _atomic_wd_2_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_2_0 := (Litex.sub _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1381) (Litex.integerToComplex _value_i8 h_1382))
      exact (Litex.subInZ _value_i7 _value_i8 h_1381 h_1382))));
  let _wd_2_4 := (Litex.number (M := M) (0 : ℂ));
  (let h_1464 : Litex.In _wd_2_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
  let h_1465 : Litex.In _wd_2_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
  let h_1466 : Litex.In _wd_2_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
  Litex.rangeFold _wd_2_0 _wd_2_1 _wd_2_2 _wd_2_3 _wd_2_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True)) h_1464 h_1465 (Litex.formulaFnInFnSet _wd_2_2) (Litex.formulaFnInFnSet _wd_2_3) h_1466 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i6 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))
  exact (Litex.integerToReal _atomic_wd_1_0 (Litex.rangeFoldInOutput _atomic_wd_1_0)))))

theorem h_1227 : (by
  let _equal_wd_1_0 := (_object_w41 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w41 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.absValue (M := M) (Litex.denote (_equal_wd_1_0).val.arg)) from congrArg (Litex.absValue (M := M)) (show Litex.denote (_equal_wd_1_0).val.arg = (Litex.denote (_equal_wd_1_0).val.arg) from rfl)) ((show (Litex.absValue (M := M) (Litex.denote (_equal_wd_1_0).val.arg)) = M.number (6 : ℂ) from (congrArg (Litex.absValue (M := M)) (show (Litex.denote (_equal_wd_1_0).val.arg) = M.number (-6 : ℂ) from (by
          let _fold := (_equal_wd_1_0).val.arg
          have _seed : Litex.denote _fold.val.seed = M.number (0 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))
          have _term_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (1 : ℂ)) = M.number (1 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => _raw_i6) (by
            intro _raw_i6 h_1487 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1487)
            have h_1487 : Litex.In _value_i6 (Litex.Z (M := M)) := h_1487
            change Litex.In _value_i6 (Litex.Z (M := M))
            exact h_1487));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := ((_equal_wd_1_0).val.arg).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (1 : ℂ)) := by change (fun (_raw_i6 : M.Value) => _raw_i6) (Litex.denote _call.val.argument) = (M.number (1 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (1 : ℂ)) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (0 : ℂ)) (M.number (1 : ℂ))) = M.number (-1 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.subValue _raw_i7 _raw_i8)) (by
            intro _raw_i7 _raw_i8 h_1496 h_1497 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1496)
            have h_1496 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1496
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1497)
            have h_1497 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1497
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1496) (Litex.integerToComplex _value_i8 h_1497))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1496) (Litex.integerToComplex _value_i8 h_1497))
              exact (Litex.subInZ _value_i7 _value_i8 h_1496 h_1497))));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := ((_equal_wd_1_0).val.arg).val.operation
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (0 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) := by change (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.subValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) = M.number (-1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _term_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (2 : ℂ)) = M.number (2 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => _raw_i6) (by
            intro _raw_i6 h_1583 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1583)
            have h_1583 : Litex.In _value_i6 (Litex.Z (M := M)) := h_1583
            change Litex.In _value_i6 (Litex.Z (M := M))
            exact h_1583));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := ((_equal_wd_1_0).val.arg).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := by change (fun (_raw_i6 : M.Value) => _raw_i6) (Litex.denote _call.val.argument) = (M.number (2 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (-1 : ℂ)) (M.number (2 : ℂ))) = M.number (-3 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.subValue _raw_i7 _raw_i8)) (by
            intro _raw_i7 _raw_i8 h_1592 h_1593 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1592)
            have h_1592 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1592
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1593)
            have h_1593 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1593
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1592) (Litex.integerToComplex _value_i8 h_1593))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1592) (Litex.integerToComplex _value_i8 h_1593))
              exact (Litex.subInZ _value_i7 _value_i8 h_1592 h_1593))));
          let _wd_1_1 := (Litex.number (M := M) (-1 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-1 : ℂ) (-1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := ((_equal_wd_1_0).val.arg).val.operation
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (-1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num : (-1 : ℂ) = (-1 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))) := by change (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.subValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))) = M.number (-3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _term_2 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (3 : ℂ)) = M.number (3 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => _raw_i6) (by
            intro _raw_i6 h_1679 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1679)
            have h_1679 : Litex.In _value_i6 (Litex.Z (M := M)) := h_1679
            change Litex.In _value_i6 (Litex.Z (M := M))
            exact h_1679));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := ((_equal_wd_1_0).val.arg).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := by change (fun (_raw_i6 : M.Value) => _raw_i6) (Litex.denote _call.val.argument) = (M.number (3 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_2 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (-3 : ℂ)) (M.number (3 : ℂ))) = M.number (-6 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.subValue _raw_i7 _raw_i8)) (by
            intro _raw_i7 _raw_i8 h_1688 h_1689 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1688)
            have h_1688 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1688
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1689)
            have h_1689 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1689
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1688) (Litex.integerToComplex _value_i8 h_1689))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1688) (Litex.integerToComplex _value_i8 h_1689))
              exact (Litex.subInZ _value_i7 _value_i8 h_1688 h_1689))));
          let _wd_1_1 := (Litex.number (M := M) (-3 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-3 : ℂ) (-3 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := ((_equal_wd_1_0).val.arg).val.operation
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (-3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))) := by change (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.subValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))) = M.number (-6 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          apply Litex.rangeFoldDenote _fold (1 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (M.number (-6 : ℂ))
          have _indices : Litex.integerFoldIndices (1 : ℤ) (3 : ℤ) = [(1 : ℤ), (2 : ℤ), (3 : ℤ)] := by decide
          norm_num [Litex.foldValue, Litex.foldApply2, _indices, _seed, _term_0, _step_0, _term_1, _step_1, _term_2, _step_2]))).trans (by
          have _numeric := Litex.absValue_number (M := M) (-6 : ℝ)
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = (6 : ℂ)))).symm)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_real_x5f_aggregates_x2f_statement_x2e_lit
