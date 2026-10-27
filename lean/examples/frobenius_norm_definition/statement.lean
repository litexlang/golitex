import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_frobenius_x5f_norm_x5f_definition_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_20 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_22 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_37 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_20 h_22)) (h_1 : (by
  let _object_h38 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_20 h_22)))
  have h_38 : Litex.In _value_i3 _object_h38 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_20 h_22) _object_h38 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_20 h_22))) h_37)
        )
    )
  exact (by
    let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
      have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
        intro _raw_i4 h_278 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_278)
        have h_278 : Litex.In _value_i4 _wd_1_0 := h_278
        have h_279 : Litex.In _value_i4 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_278).1
              )
          )
        have h_280 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_278).2.1
              )
          )
        have h_281 : Litex.Le _value_i4 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_278).2.2
              )
          )
        have h_282 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_278)
              )
          )
        change (by
          let _atomic_wd_2_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i5 h_2419 _
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_2419)
              have h_2419 : Litex.In _value_i5 _wd_2_0 := h_2419
              have h_2420 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_2419).1
                    )
                )
              have h_2421 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_2419).2.1
                    )
                )
              have h_2422 : Litex.Le _value_i5 _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_2419).2.2
                    )
                )
              have h_2423 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2419)
                    )
                )
              change (by
                let _atomic_wd_3_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                let _litex_call_arg_1 := _value_i5;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_4_1 := _wd_1_0
                  exact h_278) (by
                  let _atomic_wd_4_1 := _wd_2_0
                  exact h_2419)) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_4_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_4_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_5_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_5_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_3_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                let _litex_call_arg_1 := _value_i5;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_4_1 := _wd_1_0
                  exact h_278) (by
                  let _atomic_wd_4_1 := _wd_2_0
                  exact h_2419)) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_4_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_4_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_5_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_5_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact (by
                  let _litex_power := _atomic_wd_3_0
                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                )))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i5 h_2419 _
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_2419)
              have h_2419 : Litex.In _value_i5 _wd_2_0 := h_2419
              have h_2420 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_2419).1
                    )
                )
              have h_2421 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_2419).2.1
                    )
                )
              have h_2422 : Litex.Le _value_i5 _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_2419).2.2
                    )
                )
              have h_2423 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2419)
                    )
                )
              change (by
                let _atomic_wd_3_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                let _litex_call_arg_1 := _value_i5;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_4_1 := _wd_1_0
                  exact h_278) (by
                  let _atomic_wd_4_1 := _wd_2_0
                  exact h_2419)) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_4_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_4_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_5_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_5_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_3_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                let _litex_call_arg_1 := _value_i5;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_4_1 := _wd_1_0
                  exact h_278) (by
                  let _atomic_wd_4_1 := _wd_2_0
                  exact h_2419)) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_4_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_4_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_5_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_5_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact (by
                  let _litex_power := _atomic_wd_3_0
                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                )))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          exact (Litex.finiteAggregateOnMember _atomic_wd_2_0 .real rfl)))
      intro _litex_input _litex_domain
      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
      exact _litex_checked_return _litex_input _litex_members _litex_guard));
    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)
)), (by
  let _object_h38 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_20 h_22)))
  have h_38 : Litex.In _value_i3 _object_h38 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_20 h_22) _object_h38 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_20 h_22))) h_37)
        )
    )
  let _object_w72 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_20 h_22 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_20 h_22)
    exact h_37))
  let _object_w73 := (let _wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
  let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
    have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
      intro _raw_i6 h_8353 _
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_8353)
      have h_8353 : Litex.In _value_i6 _wd_2_0 := h_8353
      have h_8354 : Litex.In _value_i6 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_8353).1
            )
        )
      have h_8355 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_8353).2.1
            )
        )
      have h_8356 : Litex.Le _value_i6 _value_i1 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_8353).2.2
            )
        )
      have h_8357 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_8353)
            )
        )
      change (by
        let _atomic_wd_1_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
        let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
          have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
            intro _raw_i7 h_10496 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_10496)
            have h_10496 : Litex.In _value_i7 _wd_3_0 := h_10496
            have h_10497 : Litex.In _value_i7 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_10496).1
                  )
              )
            have h_10498 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_10496).2.1
                  )
              )
            have h_10499 : Litex.Le _value_i7 _value_i2 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_10496).2.2
                  )
              )
            have h_10500 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_10496)
                  )
              )
            change (by
              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
              let _litex_call_arg_1 := _value_i7;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := _wd_2_0
                exact h_8353) (by
                let _atomic_wd_3_1 := _wd_3_0
                exact h_10496)) True.intro);
              (Litex.complexAbs _wd_5_0 (by
                let _atomic_wd_3_0 := _wd_5_0
                exact (by
                  let _litex_return_call := _atomic_wd_3_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                (Litex.complexAbs _wd_5_0 (by
                  let _atomic_wd_4_0 := _wd_5_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
              let _litex_call_arg_1 := _value_i7;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := _wd_2_0
                exact h_8353) (by
                let _atomic_wd_3_1 := _wd_3_0
                exact h_10496)) True.intro);
              (Litex.complexAbs _wd_5_0 (by
                let _atomic_wd_3_0 := _wd_5_0
                exact (by
                  let _litex_return_call := _atomic_wd_3_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                (Litex.complexAbs _wd_5_0 (by
                  let _atomic_wd_4_0 := _wd_5_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              exact (by
                let _litex_power := _atomic_wd_2_0
                have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInR _litex_power _recorded_power_base
              )))
          intro _litex_input _litex_domain
          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
          exact _litex_checked_return _litex_input _litex_members _litex_guard));
        (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_1_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
        let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
          have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
            intro _raw_i7 h_10496 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_10496)
            have h_10496 : Litex.In _value_i7 _wd_3_0 := h_10496
            have h_10497 : Litex.In _value_i7 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_10496).1
                  )
              )
            have h_10498 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_10496).2.1
                  )
              )
            have h_10499 : Litex.Le _value_i7 _value_i2 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_10496).2.2
                  )
              )
            have h_10500 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_10496)
                  )
              )
            change (by
              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
              let _litex_call_arg_1 := _value_i7;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := _wd_2_0
                exact h_8353) (by
                let _atomic_wd_3_1 := _wd_3_0
                exact h_10496)) True.intro);
              (Litex.complexAbs _wd_5_0 (by
                let _atomic_wd_3_0 := _wd_5_0
                exact (by
                  let _litex_return_call := _atomic_wd_3_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                (Litex.complexAbs _wd_5_0 (by
                  let _atomic_wd_4_0 := _wd_5_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
              let _litex_call_arg_1 := _value_i7;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := _wd_2_0
                exact h_8353) (by
                let _atomic_wd_3_1 := _wd_3_0
                exact h_10496)) True.intro);
              (Litex.complexAbs _wd_5_0 (by
                let _atomic_wd_3_0 := _wd_5_0
                exact (by
                  let _litex_return_call := _atomic_wd_3_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                (Litex.complexAbs _wd_5_0 (by
                  let _atomic_wd_4_0 := _wd_5_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
              exact (by
                let _litex_power := _atomic_wd_2_0
                have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                exact Litex.powStructuralInR _litex_power _recorded_power_base
              )))
          intro _litex_input _litex_domain
          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
          exact _litex_checked_return _litex_input _litex_members _litex_guard));
        (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
    intro _litex_input _litex_domain
    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
    exact _litex_checked_return _litex_input _litex_members _litex_guard));
  (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
  (Litex.sqrt _wd_1_0 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
      have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
        intro _raw_i6 h_12312 _
        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_12312)
        have h_12312 : Litex.In _value_i6 _wd_2_0 := h_12312
        have h_12313 : Litex.In _value_i6 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_12312).1
              )
          )
        have h_12314 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_12312).2.1
              )
          )
        have h_12315 : Litex.Le _value_i6 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_12312).2.2
              )
          )
        have h_12316 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_12312)
              )
          )
        change (by
          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i7 h_14455 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_14455)
              have h_14455 : Litex.In _value_i7 _wd_3_0 := h_14455
              have h_14456 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_14455).1
                    )
                )
              have h_14457 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_14455).2.1
                    )
                )
              have h_14458 : Litex.Le _value_i7 _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_14455).2.2
                    )
                )
              have h_14459 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_14455)
                    )
                )
              change (by
                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                let _litex_call_arg_1 := _value_i7;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_4_1 := _wd_2_0
                  exact h_12312) (by
                  let _atomic_wd_4_1 := _wd_3_0
                  exact h_14455)) True.intro);
                (Litex.complexAbs _wd_5_0 (by
                  let _atomic_wd_4_0 := _wd_5_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                  (Litex.complexAbs _wd_5_0 (by
                    let _atomic_wd_5_0 := _wd_5_0
                    exact (by
                      let _litex_return_call := _atomic_wd_5_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                let _litex_call_arg_1 := _value_i7;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_4_1 := _wd_2_0
                  exact h_12312) (by
                  let _atomic_wd_4_1 := _wd_3_0
                  exact h_14455)) True.intro);
                (Litex.complexAbs _wd_5_0 (by
                  let _atomic_wd_4_0 := _wd_5_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                  (Litex.complexAbs _wd_5_0 (by
                    let _atomic_wd_5_0 := _wd_5_0
                    exact (by
                      let _litex_return_call := _atomic_wd_5_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact (by
                  let _litex_power := _atomic_wd_3_0
                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                )))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i7 h_14455 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_14455)
              have h_14455 : Litex.In _value_i7 _wd_3_0 := h_14455
              have h_14456 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_14455).1
                    )
                )
              have h_14457 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_14455).2.1
                    )
                )
              have h_14458 : Litex.Le _value_i7 _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_14455).2.2
                    )
                )
              have h_14459 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_14455)
                    )
                )
              change (by
                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                let _litex_call_arg_1 := _value_i7;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_4_1 := _wd_2_0
                  exact h_12312) (by
                  let _atomic_wd_4_1 := _wd_3_0
                  exact h_14455)) True.intro);
                (Litex.complexAbs _wd_5_0 (by
                  let _atomic_wd_4_0 := _wd_5_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                  (Litex.complexAbs _wd_5_0 (by
                    let _atomic_wd_5_0 := _wd_5_0
                    exact (by
                      let _litex_return_call := _atomic_wd_5_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                let _litex_call_arg_1 := _value_i7;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_4_1 := _wd_2_0
                  exact h_12312) (by
                  let _atomic_wd_4_1 := _wd_3_0
                  exact h_14455)) True.intro);
                (Litex.complexAbs _wd_5_0 (by
                  let _atomic_wd_4_0 := _wd_5_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                  (Litex.complexAbs _wd_5_0 (by
                    let _atomic_wd_5_0 := _wd_5_0
                    exact (by
                      let _litex_return_call := _atomic_wd_5_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact (by
                  let _litex_power := _atomic_wd_3_0
                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                )))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          exact (Litex.finiteAggregateOnMember _atomic_wd_2_0 .real rfl)))
      intro _litex_input _litex_domain
      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
      exact _litex_checked_return _litex_input _litex_members _litex_guard));
    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
    exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)) (by
    let _atomic_wd_1_1 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
      have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
        intro _raw_i6 h_16356 _
        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_16356)
        have h_16356 : Litex.In _value_i6 _wd_2_0 := h_16356
        have h_16357 : Litex.In _value_i6 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_16356).1
              )
          )
        have h_16358 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_16356).2.1
              )
          )
        have h_16359 : Litex.Le _value_i6 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_16356).2.2
              )
          )
        have h_16360 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_16356)
              )
          )
        change (by
          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i7 h_18499 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_18499)
              have h_18499 : Litex.In _value_i7 _wd_3_0 := h_18499
              have h_18500 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_18499).1
                    )
                )
              have h_18501 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_18499).2.1
                    )
                )
              have h_18502 : Litex.Le _value_i7 _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_18499).2.2
                    )
                )
              have h_18503 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_18499)
                    )
                )
              change (by
                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                let _litex_call_arg_1 := _value_i7;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_4_1 := _wd_2_0
                  exact h_16356) (by
                  let _atomic_wd_4_1 := _wd_3_0
                  exact h_18499)) True.intro);
                (Litex.complexAbs _wd_5_0 (by
                  let _atomic_wd_4_0 := _wd_5_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                  (Litex.complexAbs _wd_5_0 (by
                    let _atomic_wd_5_0 := _wd_5_0
                    exact (by
                      let _litex_return_call := _atomic_wd_5_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                let _litex_call_arg_1 := _value_i7;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_4_1 := _wd_2_0
                  exact h_16356) (by
                  let _atomic_wd_4_1 := _wd_3_0
                  exact h_18499)) True.intro);
                (Litex.complexAbs _wd_5_0 (by
                  let _atomic_wd_4_0 := _wd_5_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                  (Litex.complexAbs _wd_5_0 (by
                    let _atomic_wd_5_0 := _wd_5_0
                    exact (by
                      let _litex_return_call := _atomic_wd_5_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact (by
                  let _litex_power := _atomic_wd_3_0
                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                )))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i7 h_18499 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_18499)
              have h_18499 : Litex.In _value_i7 _wd_3_0 := h_18499
              have h_18500 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_18499).1
                    )
                )
              have h_18501 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_18499).2.1
                    )
                )
              have h_18502 : Litex.Le _value_i7 _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_18499).2.2
                    )
                )
              have h_18503 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_18499)
                    )
                )
              change (by
                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                let _litex_call_arg_1 := _value_i7;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_4_1 := _wd_2_0
                  exact h_16356) (by
                  let _atomic_wd_4_1 := _wd_3_0
                  exact h_18499)) True.intro);
                (Litex.complexAbs _wd_5_0 (by
                  let _atomic_wd_4_0 := _wd_5_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                  (Litex.complexAbs _wd_5_0 (by
                    let _atomic_wd_5_0 := _wd_5_0
                    exact (by
                      let _litex_return_call := _atomic_wd_5_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                let _litex_call_arg_1 := _value_i7;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_4_1 := _wd_2_0
                  exact h_16356) (by
                  let _atomic_wd_4_1 := _wd_3_0
                  exact h_18499)) True.intro);
                (Litex.complexAbs _wd_5_0 (by
                  let _atomic_wd_4_0 := _wd_5_0
                  exact (by
                    let _litex_return_call := _atomic_wd_4_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                  (Litex.complexAbs _wd_5_0 (by
                    let _atomic_wd_5_0 := _wd_5_0
                    exact (by
                      let _litex_return_call := _atomic_wd_5_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact (by
                  let _litex_power := _atomic_wd_3_0
                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                )))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          exact (Litex.finiteAggregateOnMember _atomic_wd_2_0 .real rfl)))
      intro _litex_input _litex_domain
      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
      exact _litex_checked_return _litex_input _litex_members _litex_guard));
    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
    exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
      have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
        intro _raw_i4 h_4246 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_4246)
        have h_4246 : Litex.In _value_i4 _wd_1_0 := h_4246
        have h_4247 : Litex.In _value_i4 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).1
              )
          )
        have h_4248 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.1
              )
          )
        have h_4249 : Litex.Le _value_i4 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.2
              )
          )
        have h_4250 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4246)
              )
          )
        change (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i5 h_6385 _
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                    )
                )
              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                    )
                )
              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                    )
                )
              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                    )
                )
              change (by
                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                let _litex_call_arg_1 := _value_i5;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_3_1 := _wd_1_0
                  exact h_4246) (by
                  let _atomic_wd_3_1 := _wd_2_0
                  exact h_6385)) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_3_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_3_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_4_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_4_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                let _litex_call_arg_1 := _value_i5;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_3_1 := _wd_1_0
                  exact h_4246) (by
                  let _atomic_wd_3_1 := _wd_2_0
                  exact h_6385)) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_3_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_3_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_4_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_4_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                )))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i5 h_6385 _
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                    )
                )
              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                    )
                )
              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                    )
                )
              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                    )
                )
              change (by
                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                let _litex_call_arg_1 := _value_i5;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_3_1 := _wd_1_0
                  exact h_4246) (by
                  let _atomic_wd_3_1 := _wd_2_0
                  exact h_6385)) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_3_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_3_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_4_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_4_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                let _litex_call_arg_1 := _value_i5;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_3_1 := _wd_1_0
                  exact h_4246) (by
                  let _atomic_wd_3_1 := _wd_2_0
                  exact h_6385)) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_3_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_3_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_4_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_4_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                )))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
      intro _litex_input _litex_domain
      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
      exact _litex_checked_return _litex_input _litex_members _litex_guard));
    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
      have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
        intro _raw_i4 h_4246 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_4246)
        have h_4246 : Litex.In _value_i4 _wd_1_0 := h_4246
        have h_4247 : Litex.In _value_i4 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).1
              )
          )
        have h_4248 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.1
              )
          )
        have h_4249 : Litex.Le _value_i4 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.2
              )
          )
        have h_4250 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4246)
              )
          )
        change (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i5 h_6385 _
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                    )
                )
              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                    )
                )
              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                    )
                )
              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                    )
                )
              change (by
                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                let _litex_call_arg_1 := _value_i5;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_3_1 := _wd_1_0
                  exact h_4246) (by
                  let _atomic_wd_3_1 := _wd_2_0
                  exact h_6385)) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_3_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_3_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_4_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_4_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                let _litex_call_arg_1 := _value_i5;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_3_1 := _wd_1_0
                  exact h_4246) (by
                  let _atomic_wd_3_1 := _wd_2_0
                  exact h_6385)) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_3_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_3_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_4_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_4_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                )))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i5 h_6385 _
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                    )
                )
              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                    )
                )
              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                    )
                )
              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                    )
                )
              change (by
                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                let _litex_call_arg_1 := _value_i5;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_3_1 := _wd_1_0
                  exact h_4246) (by
                  let _atomic_wd_3_1 := _wd_2_0
                  exact h_6385)) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_3_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_3_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_4_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_4_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                let _litex_call_arg_1 := _value_i5;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_3_1 := _wd_1_0
                  exact h_4246) (by
                  let _atomic_wd_3_1 := _wd_2_0
                  exact h_6385)) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_3_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_3_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_4_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_4_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact (by
                  let _litex_power := _atomic_wd_2_0
                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                )))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
      intro _litex_input _litex_domain
      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
      exact _litex_checked_return _litex_input _litex_members _litex_guard));
    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
      let _right := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_1))))
  exact (by
    let _equal_wd_1_0 := _object_w72
    let _equal_wd_1_1 := _object_w73
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_20 _Host_i2 _rep_i2 _value_i2 h_22 _Host_i3 _rep_i3 _value_i3 h_37 h_1
          have h_21 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_20)
                )
            )
          have h_23 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_22)
                )
            )
          let _object_h38 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_20 h_22)))
          have h_38 : Litex.In _value_i3 _object_h38 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_20 h_22) _object_h38 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_20 h_22))) h_37)
                )
            )
          let _object_w72 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_20 h_22 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_20 h_22)
            exact h_37))
          let _object_w73 := (let _wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i6 h_8353 _
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_8353)
              have h_8353 : Litex.In _value_i6 _wd_2_0 := h_8353
              have h_8354 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_8353).1
                    )
                )
              have h_8355 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_8353).2.1
                    )
                )
              have h_8356 : Litex.Le _value_i6 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_8353).2.2
                    )
                )
              have h_8357 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_8353)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
                  have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
                    intro _raw_i7 h_10496 _
                    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_10496)
                    have h_10496 : Litex.In _value_i7 _wd_3_0 := h_10496
                    have h_10497 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_10496).1
                          )
                      )
                    have h_10498 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_10496).2.1
                          )
                      )
                    have h_10499 : Litex.Le _value_i7 _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_10496).2.2
                          )
                      )
                    have h_10500 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_10496)
                          )
                      )
                    change (by
                      let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                      let _litex_call_arg_1 := _value_i7;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                        have _finiteProof_0 := (Litex.isSet _wd_2_0)
                        have _finiteProof_1 := (Litex.isSet _wd_3_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := _wd_2_0
                        exact h_8353) (by
                        let _atomic_wd_3_1 := _wd_3_0
                        exact h_10496)) True.intro);
                      (Litex.complexAbs _wd_5_0 (by
                        let _atomic_wd_3_0 := _wd_5_0
                        exact (by
                          let _litex_return_call := _atomic_wd_3_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                      let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                      (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                        let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                        (Litex.complexAbs _wd_5_0 (by
                          let _atomic_wd_4_0 := _wd_5_0
                          exact (by
                            let _litex_return_call := _atomic_wd_4_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                      exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                    exact (by
                      let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                      let _litex_call_arg_1 := _value_i7;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                        have _finiteProof_0 := (Litex.isSet _wd_2_0)
                        have _finiteProof_1 := (Litex.isSet _wd_3_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := _wd_2_0
                        exact h_8353) (by
                        let _atomic_wd_3_1 := _wd_3_0
                        exact h_10496)) True.intro);
                      (Litex.complexAbs _wd_5_0 (by
                        let _atomic_wd_3_0 := _wd_5_0
                        exact (by
                          let _litex_return_call := _atomic_wd_3_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                      let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                      (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                        let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                        (Litex.complexAbs _wd_5_0 (by
                          let _atomic_wd_4_0 := _wd_5_0
                          exact (by
                            let _litex_return_call := _atomic_wd_4_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                      exact (by
                        let _litex_power := _atomic_wd_2_0
                        have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInR _litex_power _recorded_power_base
                      )))
                  intro _litex_input _litex_domain
                  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                  exact _litex_checked_return _litex_input _litex_members _litex_guard));
                (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                  exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                  exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
                  have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
                    intro _raw_i7 h_10496 _
                    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_10496)
                    have h_10496 : Litex.In _value_i7 _wd_3_0 := h_10496
                    have h_10497 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_10496).1
                          )
                      )
                    have h_10498 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_10496).2.1
                          )
                      )
                    have h_10499 : Litex.Le _value_i7 _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_10496).2.2
                          )
                      )
                    have h_10500 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_10496)
                          )
                      )
                    change (by
                      let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                      let _litex_call_arg_1 := _value_i7;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                        have _finiteProof_0 := (Litex.isSet _wd_2_0)
                        have _finiteProof_1 := (Litex.isSet _wd_3_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := _wd_2_0
                        exact h_8353) (by
                        let _atomic_wd_3_1 := _wd_3_0
                        exact h_10496)) True.intro);
                      (Litex.complexAbs _wd_5_0 (by
                        let _atomic_wd_3_0 := _wd_5_0
                        exact (by
                          let _litex_return_call := _atomic_wd_3_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                      let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                      (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                        let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                        (Litex.complexAbs _wd_5_0 (by
                          let _atomic_wd_4_0 := _wd_5_0
                          exact (by
                            let _litex_return_call := _atomic_wd_4_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                      exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                    exact (by
                      let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                      let _litex_call_arg_1 := _value_i7;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                        have _finiteProof_0 := (Litex.isSet _wd_2_0)
                        have _finiteProof_1 := (Litex.isSet _wd_3_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := _wd_2_0
                        exact h_8353) (by
                        let _atomic_wd_3_1 := _wd_3_0
                        exact h_10496)) True.intro);
                      (Litex.complexAbs _wd_5_0 (by
                        let _atomic_wd_3_0 := _wd_5_0
                        exact (by
                          let _litex_return_call := _atomic_wd_3_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                      let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                      (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                        let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                        (Litex.complexAbs _wd_5_0 (by
                          let _atomic_wd_4_0 := _wd_5_0
                          exact (by
                            let _litex_return_call := _atomic_wd_4_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                      exact (by
                        let _litex_power := _atomic_wd_2_0
                        have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                        have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                        have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                        have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                        exact Litex.powStructuralInR _litex_power _recorded_power_base
                      )))
                  intro _litex_input _litex_domain
                  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                  exact _litex_checked_return _litex_input _litex_members _litex_guard));
                (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                  exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                  exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
            exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
            exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
          (Litex.sqrt _wd_1_0 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
            let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
              have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                intro _raw_i6 h_12312 _
                let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_12312)
                have h_12312 : Litex.In _value_i6 _wd_2_0 := h_12312
                have h_12313 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_12312).1
                      )
                  )
                have h_12314 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_12312).2.1
                      )
                  )
                have h_12315 : Litex.Le _value_i6 _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_12312).2.2
                      )
                  )
                have h_12316 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_12312)
                      )
                  )
                change (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                  let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i7 h_14455 _
                      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_14455)
                      have h_14455 : Litex.In _value_i7 _wd_3_0 := h_14455
                      have h_14456 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_14455).1
                            )
                        )
                      have h_14457 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_14455).2.1
                            )
                        )
                      have h_14458 : Litex.Le _value_i7 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_14455).2.2
                            )
                        )
                      have h_14459 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_14455)
                            )
                        )
                      change (by
                        let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_2_0)
                          have _finiteProof_1 := (Litex.isSet _wd_3_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_4_1 := _wd_2_0
                          exact h_12312) (by
                          let _atomic_wd_4_1 := _wd_3_0
                          exact h_14455)) True.intro);
                        (Litex.complexAbs _wd_5_0 (by
                          let _atomic_wd_4_0 := _wd_5_0
                          exact (by
                            let _litex_return_call := _atomic_wd_4_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                          let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                          (Litex.complexAbs _wd_5_0 (by
                            let _atomic_wd_5_0 := _wd_5_0
                            exact (by
                              let _litex_return_call := _atomic_wd_5_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_2_0)
                          have _finiteProof_1 := (Litex.isSet _wd_3_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_4_1 := _wd_2_0
                          exact h_12312) (by
                          let _atomic_wd_4_1 := _wd_3_0
                          exact h_14455)) True.intro);
                        (Litex.complexAbs _wd_5_0 (by
                          let _atomic_wd_4_0 := _wd_5_0
                          exact (by
                            let _litex_return_call := _atomic_wd_4_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                          let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                          (Litex.complexAbs _wd_5_0 (by
                            let _atomic_wd_5_0 := _wd_5_0
                            exact (by
                              let _litex_return_call := _atomic_wd_5_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_3_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                    let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                  exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                  let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i7 h_14455 _
                      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_14455)
                      have h_14455 : Litex.In _value_i7 _wd_3_0 := h_14455
                      have h_14456 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_14455).1
                            )
                        )
                      have h_14457 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_14455).2.1
                            )
                        )
                      have h_14458 : Litex.Le _value_i7 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_14455).2.2
                            )
                        )
                      have h_14459 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_14455)
                            )
                        )
                      change (by
                        let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_2_0)
                          have _finiteProof_1 := (Litex.isSet _wd_3_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_4_1 := _wd_2_0
                          exact h_12312) (by
                          let _atomic_wd_4_1 := _wd_3_0
                          exact h_14455)) True.intro);
                        (Litex.complexAbs _wd_5_0 (by
                          let _atomic_wd_4_0 := _wd_5_0
                          exact (by
                            let _litex_return_call := _atomic_wd_4_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                          let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                          (Litex.complexAbs _wd_5_0 (by
                            let _atomic_wd_5_0 := _wd_5_0
                            exact (by
                              let _litex_return_call := _atomic_wd_5_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_2_0)
                          have _finiteProof_1 := (Litex.isSet _wd_3_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_4_1 := _wd_2_0
                          exact h_12312) (by
                          let _atomic_wd_4_1 := _wd_3_0
                          exact h_14455)) True.intro);
                        (Litex.complexAbs _wd_5_0 (by
                          let _atomic_wd_4_0 := _wd_5_0
                          exact (by
                            let _litex_return_call := _atomic_wd_4_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                          let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                          (Litex.complexAbs _wd_5_0 (by
                            let _atomic_wd_5_0 := _wd_5_0
                            exact (by
                              let _litex_return_call := _atomic_wd_5_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_3_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                    let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                  exact (Litex.finiteAggregateOnMember _atomic_wd_2_0 .real rfl)))
              intro _litex_input _litex_domain
              obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
              exact _litex_checked_return _litex_input _litex_members _litex_guard));
            (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
              let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
              exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
              let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
              let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
              exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
            exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)) (by
            let _atomic_wd_1_1 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
            let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
              have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                intro _raw_i6 h_16356 _
                let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_16356)
                have h_16356 : Litex.In _value_i6 _wd_2_0 := h_16356
                have h_16357 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_16356).1
                      )
                  )
                have h_16358 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_16356).2.1
                      )
                  )
                have h_16359 : Litex.Le _value_i6 _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_16356).2.2
                      )
                  )
                have h_16360 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_16356)
                      )
                  )
                change (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                  let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i7 h_18499 _
                      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_18499)
                      have h_18499 : Litex.In _value_i7 _wd_3_0 := h_18499
                      have h_18500 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_18499).1
                            )
                        )
                      have h_18501 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_18499).2.1
                            )
                        )
                      have h_18502 : Litex.Le _value_i7 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_18499).2.2
                            )
                        )
                      have h_18503 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_18499)
                            )
                        )
                      change (by
                        let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_2_0)
                          have _finiteProof_1 := (Litex.isSet _wd_3_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_4_1 := _wd_2_0
                          exact h_16356) (by
                          let _atomic_wd_4_1 := _wd_3_0
                          exact h_18499)) True.intro);
                        (Litex.complexAbs _wd_5_0 (by
                          let _atomic_wd_4_0 := _wd_5_0
                          exact (by
                            let _litex_return_call := _atomic_wd_4_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                          let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                          (Litex.complexAbs _wd_5_0 (by
                            let _atomic_wd_5_0 := _wd_5_0
                            exact (by
                              let _litex_return_call := _atomic_wd_5_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_2_0)
                          have _finiteProof_1 := (Litex.isSet _wd_3_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_4_1 := _wd_2_0
                          exact h_16356) (by
                          let _atomic_wd_4_1 := _wd_3_0
                          exact h_18499)) True.intro);
                        (Litex.complexAbs _wd_5_0 (by
                          let _atomic_wd_4_0 := _wd_5_0
                          exact (by
                            let _litex_return_call := _atomic_wd_4_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                          let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                          (Litex.complexAbs _wd_5_0 (by
                            let _atomic_wd_5_0 := _wd_5_0
                            exact (by
                              let _litex_return_call := _atomic_wd_5_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_3_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                    let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                  exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                  let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i7 h_18499 _
                      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_18499)
                      have h_18499 : Litex.In _value_i7 _wd_3_0 := h_18499
                      have h_18500 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_18499).1
                            )
                        )
                      have h_18501 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_18499).2.1
                            )
                        )
                      have h_18502 : Litex.Le _value_i7 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_18499).2.2
                            )
                        )
                      have h_18503 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_18499)
                            )
                        )
                      change (by
                        let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_2_0)
                          have _finiteProof_1 := (Litex.isSet _wd_3_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_4_1 := _wd_2_0
                          exact h_16356) (by
                          let _atomic_wd_4_1 := _wd_3_0
                          exact h_18499)) True.intro);
                        (Litex.complexAbs _wd_5_0 (by
                          let _atomic_wd_4_0 := _wd_5_0
                          exact (by
                            let _litex_return_call := _atomic_wd_4_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                          let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                          (Litex.complexAbs _wd_5_0 (by
                            let _atomic_wd_5_0 := _wd_5_0
                            exact (by
                              let _litex_return_call := _atomic_wd_5_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_2_0)
                          have _finiteProof_1 := (Litex.isSet _wd_3_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_4_1 := _wd_2_0
                          exact h_16356) (by
                          let _atomic_wd_4_1 := _wd_3_0
                          exact h_18499)) True.intro);
                        (Litex.complexAbs _wd_5_0 (by
                          let _atomic_wd_4_0 := _wd_5_0
                          exact (by
                            let _litex_return_call := _atomic_wd_4_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                          let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                          (Litex.complexAbs _wd_5_0 (by
                            let _atomic_wd_5_0 := _wd_5_0
                            exact (by
                              let _litex_return_call := _atomic_wd_5_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_3_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                    let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                  exact (Litex.finiteAggregateOnMember _atomic_wd_2_0 .real rfl)))
              intro _litex_input _litex_domain
              obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
              exact _litex_checked_return _litex_input _litex_members _litex_guard));
            (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
              let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
              exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
              let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
              let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
              exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
            exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
            let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
              have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                intro _raw_i4 h_4246 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_4246)
                have h_4246 : Litex.In _value_i4 _wd_1_0 := h_4246
                have h_4247 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).1
                      )
                  )
                have h_4248 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.1
                      )
                  )
                have h_4249 : Litex.Le _value_i4 _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.2
                      )
                  )
                have h_4250 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4246)
                      )
                  )
                change (by
                  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                  let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i5 h_6385 _
                      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                      have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                      have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                            )
                        )
                      have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                            )
                        )
                      have h_6388 : Litex.Le _value_i5 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                            )
                        )
                      have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                            )
                        )
                      change (by
                        let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                        let _litex_call_arg_1 := _value_i5;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_2_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_3_1 := _wd_1_0
                          exact h_4246) (by
                          let _atomic_wd_3_1 := _wd_2_0
                          exact h_6385)) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_3_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_3_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_4_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_4_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                        let _litex_call_arg_1 := _value_i5;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_2_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_3_1 := _wd_1_0
                          exact h_4246) (by
                          let _atomic_wd_3_1 := _wd_2_0
                          exact h_6385)) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_3_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_3_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_4_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_4_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_2_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                    let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                  let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i5 h_6385 _
                      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                      have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                      have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                            )
                        )
                      have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                            )
                        )
                      have h_6388 : Litex.Le _value_i5 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                            )
                        )
                      have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                            )
                        )
                      change (by
                        let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                        let _litex_call_arg_1 := _value_i5;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_2_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_3_1 := _wd_1_0
                          exact h_4246) (by
                          let _atomic_wd_3_1 := _wd_2_0
                          exact h_6385)) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_3_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_3_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_4_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_4_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                        let _litex_call_arg_1 := _value_i5;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_2_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_3_1 := _wd_1_0
                          exact h_4246) (by
                          let _atomic_wd_3_1 := _wd_2_0
                          exact h_6385)) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_3_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_3_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_4_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_4_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_2_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                    let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                  exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
              intro _litex_input _litex_domain
              obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
              exact _litex_checked_return _litex_input _litex_members _litex_guard));
            (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
              let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
              exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
              let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
              exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
            let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
              have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                intro _raw_i4 h_4246 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_4246)
                have h_4246 : Litex.In _value_i4 _wd_1_0 := h_4246
                have h_4247 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).1
                      )
                  )
                have h_4248 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.1
                      )
                  )
                have h_4249 : Litex.Le _value_i4 _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.2
                      )
                  )
                have h_4250 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4246)
                      )
                  )
                change (by
                  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                  let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i5 h_6385 _
                      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                      have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                      have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                            )
                        )
                      have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                            )
                        )
                      have h_6388 : Litex.Le _value_i5 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                            )
                        )
                      have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                            )
                        )
                      change (by
                        let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                        let _litex_call_arg_1 := _value_i5;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_2_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_3_1 := _wd_1_0
                          exact h_4246) (by
                          let _atomic_wd_3_1 := _wd_2_0
                          exact h_6385)) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_3_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_3_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_4_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_4_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                        let _litex_call_arg_1 := _value_i5;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_2_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_3_1 := _wd_1_0
                          exact h_4246) (by
                          let _atomic_wd_3_1 := _wd_2_0
                          exact h_6385)) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_3_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_3_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_4_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_4_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_2_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                    let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                  let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i5 h_6385 _
                      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                      have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                      have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                            )
                        )
                      have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                            )
                        )
                      have h_6388 : Litex.Le _value_i5 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                            )
                        )
                      have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                            )
                        )
                      change (by
                        let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                        let _litex_call_arg_1 := _value_i5;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_2_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_3_1 := _wd_1_0
                          exact h_4246) (by
                          let _atomic_wd_3_1 := _wd_2_0
                          exact h_6385)) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_3_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_3_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_4_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_4_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                        let _litex_call_arg_1 := _value_i5;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_2_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_3_1 := _wd_1_0
                          exact h_4246) (by
                          let _atomic_wd_3_1 := _wd_2_0
                          exact h_6385)) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_3_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_3_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_4_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_4_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_2_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                    let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                    exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                  exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
              intro _litex_input _litex_domain
              obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
              exact _litex_checked_return _litex_input _litex_members _litex_guard));
            (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
              let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
              exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
              let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
              exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
              let _right := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_1))))
          have h_2 : (by
            let _equal_wd_1_0 := _object_w72
            let _equal_wd_1_1 := _object_w73
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w72;
                  let _equal_wd_1_1 := _object_w73;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _norm := _equal_wd_1_0
                    let _expanded := (let _wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                  let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i10, _raw_i11]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i10, _raw_i11]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i10 h_20380 _
                      let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_20380)
                      have h_20380 : Litex.In _value_i10 _wd_2_0 := h_20380
                      have h_20381 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_20380).1
                            )
                        )
                      have h_20382 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_20380).2.1
                            )
                        )
                      have h_20383 : Litex.Le _value_i10 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_20380).2.2
                            )
                        )
                      have h_20384 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_20380)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                        let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _wd_3_0) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem ((fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _raw_i11) (Litex.denote (Litex.R (M := M))) := (by
                            intro _raw_i11 h_22521 _
                            let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_22521)
                            have h_22521 : Litex.In _value_i11 _wd_3_0 := h_22521
                            have h_22522 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_22521).1
                                  )
                              )
                            have h_22523 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_22521).2.1
                                  )
                              )
                            have h_22524 : Litex.Le _value_i11 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_22521).2.2
                                  )
                              )
                            have h_22525 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_3_0 _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_22521)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                              let _litex_call_arg_1 := _value_i11;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_20380) (by
                                let _atomic_wd_3_1 := _wd_3_0
                                exact h_22521)) True.intro);
                              (Litex.complexAbs _wd_5_0 (by
                                let _atomic_wd_3_0 := _wd_5_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                            exact (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                              let _litex_call_arg_1 := _value_i11;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_20380) (by
                                let _atomic_wd_3_1 := _wd_3_0
                                exact h_22521)) True.intro);
                              (Litex.complexAbs _wd_5_0 (by
                                let _atomic_wd_3_0 := _wd_5_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                              exact (by
                                let _litex_power := _atomic_wd_2_0
                                have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                exact Litex.powStructuralInR _litex_power _recorded_power_base
                              )))
                          intro _litex_input _litex_domain
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                        let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _wd_3_0) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem ((fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _raw_i11) (Litex.denote (Litex.R (M := M))) := (by
                            intro _raw_i11 h_22521 _
                            let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_22521)
                            have h_22521 : Litex.In _value_i11 _wd_3_0 := h_22521
                            have h_22522 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_22521).1
                                  )
                              )
                            have h_22523 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_22521).2.1
                                  )
                              )
                            have h_22524 : Litex.Le _value_i11 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_22521).2.2
                                  )
                              )
                            have h_22525 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_3_0 _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_22521)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                              let _litex_call_arg_1 := _value_i11;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_20380) (by
                                let _atomic_wd_3_1 := _wd_3_0
                                exact h_22521)) True.intro);
                              (Litex.complexAbs _wd_5_0 (by
                                let _atomic_wd_3_0 := _wd_5_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                            exact (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                              let _litex_call_arg_1 := _value_i11;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_20380) (by
                                let _atomic_wd_3_1 := _wd_3_0
                                exact h_22521)) True.intro);
                              (Litex.complexAbs _wd_5_0 (by
                                let _atomic_wd_3_0 := _wd_5_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                              exact (by
                                let _litex_power := _atomic_wd_2_0
                                have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                exact Litex.powStructuralInR _litex_power _recorded_power_base
                              )))
                          intro _litex_input _litex_domain
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
                  (Litex.sqrt _wd_1_0 (by
                    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i10, _raw_i11]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i10, _raw_i11]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i10 h_24336 _
                        let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_24336)
                        have h_24336 : Litex.In _value_i10 _wd_2_0 := h_24336
                        have h_24337 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_24336).1
                              )
                          )
                        have h_24338 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_24336).2.1
                              )
                          )
                        have h_24339 : Litex.Le _value_i10 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_24336).2.2
                              )
                          )
                        have h_24340 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_24336)
                              )
                          )
                        change (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _wd_3_0) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem ((fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _raw_i11) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i11 h_26477 _
                              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_26477)
                              have h_26477 : Litex.In _value_i11 _wd_3_0 := h_26477
                              have h_26478 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_26477).1
                                    )
                                )
                              have h_26479 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_26477).2.1
                                    )
                                )
                              have h_26480 : Litex.Le _value_i11 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_26477).2.2
                                    )
                                )
                              have h_26481 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_3_0 _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_26477)
                                    )
                                )
                              change (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_24336) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_26477)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_24336) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_26477)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_3_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _wd_3_0) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem ((fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _raw_i11) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i11 h_26477 _
                              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_26477)
                              have h_26477 : Litex.In _value_i11 _wd_3_0 := h_26477
                              have h_26478 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_26477).1
                                    )
                                )
                              have h_26479 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_26477).2.1
                                    )
                                )
                              have h_26480 : Litex.Le _value_i11 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_26477).2.2
                                    )
                                )
                              have h_26481 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_3_0 _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_26477)
                                    )
                                )
                              change (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_24336) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_26477)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_24336) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_26477)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_3_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_2_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)) (by
                    let _atomic_wd_1_1 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i10, _raw_i11]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i10, _raw_i11]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i10 h_28377 _
                        let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_28377)
                        have h_28377 : Litex.In _value_i10 _wd_2_0 := h_28377
                        have h_28378 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_28377).1
                              )
                          )
                        have h_28379 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_28377).2.1
                              )
                          )
                        have h_28380 : Litex.Le _value_i10 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_28377).2.2
                              )
                          )
                        have h_28381 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_28377)
                              )
                          )
                        change (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _wd_3_0) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem ((fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _raw_i11) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i11 h_30518 _
                              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_30518)
                              have h_30518 : Litex.In _value_i11 _wd_3_0 := h_30518
                              have h_30519 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_30518).1
                                    )
                                )
                              have h_30520 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_30518).2.1
                                    )
                                )
                              have h_30521 : Litex.Le _value_i11 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_30518).2.2
                                    )
                                )
                              have h_30522 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_3_0 _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_30518)
                                    )
                                )
                              change (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_28377) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_30518)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_28377) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_30518)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_3_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _wd_3_0) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem ((fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _raw_i11) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i11 h_30518 _
                              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_30518)
                              have h_30518 : Litex.In _value_i11 _wd_3_0 := h_30518
                              have h_30519 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_30518).1
                                    )
                                )
                              have h_30520 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_30518).2.1
                                    )
                                )
                              have h_30521 : Litex.Le _value_i11 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_30518).2.2
                                    )
                                )
                              have h_30522 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_3_0 _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_30518)
                                    )
                                )
                              change (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_28377) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_30518)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_28377) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_30518)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_3_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_2_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i4 h_4246 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_4246)
                        have h_4246 : Litex.In _value_i4 _wd_1_0 := h_4246
                        have h_4247 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).1
                              )
                          )
                        have h_4248 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.1
                              )
                          )
                        have h_4249 : Litex.Le _value_i4 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.2
                              )
                          )
                        have h_4250 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4246)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i5 h_6385 _
                              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                                    )
                                )
                              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                                    )
                                )
                              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                                    )
                                )
                              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_2_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i5 h_6385 _
                              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                                    )
                                )
                              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                                    )
                                )
                              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                                    )
                                )
                              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_2_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                      let _left := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i4 h_4246 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_4246)
                        have h_4246 : Litex.In _value_i4 _wd_1_0 := h_4246
                        have h_4247 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).1
                              )
                          )
                        have h_4248 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.1
                              )
                          )
                        have h_4249 : Litex.Le _value_i4 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.2
                              )
                          )
                        have h_4250 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4246)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i5 h_6385 _
                              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                                    )
                                )
                              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                                    )
                                )
                              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                                    )
                                )
                              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_2_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i5 h_6385 _
                              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                                    )
                                )
                              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                                    )
                                )
                              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                                    )
                                )
                              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_2_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                      let _right := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) h_1))))
                    have _definition : Litex.Same _norm _expanded := Litex.frobeniusNormFormula _norm (_expanded.val.arg).val.function (by rfl) (by rfl)
                    exact (_definition.trans (let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                  let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i10, _raw_i11]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i10, _raw_i11]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i10 h_20380 _
                      let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_20380)
                      have h_20380 : Litex.In _value_i10 _wd_2_0 := h_20380
                      have h_20381 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_20380).1
                            )
                        )
                      have h_20382 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_20380).2.1
                            )
                        )
                      have h_20383 : Litex.Le _value_i10 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_20380).2.2
                            )
                        )
                      have h_20384 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_20380)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                        let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _wd_3_0) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem ((fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _raw_i11) (Litex.denote (Litex.R (M := M))) := (by
                            intro _raw_i11 h_22521 _
                            let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_22521)
                            have h_22521 : Litex.In _value_i11 _wd_3_0 := h_22521
                            have h_22522 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_22521).1
                                  )
                              )
                            have h_22523 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_22521).2.1
                                  )
                              )
                            have h_22524 : Litex.Le _value_i11 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_22521).2.2
                                  )
                              )
                            have h_22525 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_3_0 _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_22521)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                              let _litex_call_arg_1 := _value_i11;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_20380) (by
                                let _atomic_wd_3_1 := _wd_3_0
                                exact h_22521)) True.intro);
                              (Litex.complexAbs _wd_5_0 (by
                                let _atomic_wd_3_0 := _wd_5_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                            exact (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                              let _litex_call_arg_1 := _value_i11;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_20380) (by
                                let _atomic_wd_3_1 := _wd_3_0
                                exact h_22521)) True.intro);
                              (Litex.complexAbs _wd_5_0 (by
                                let _atomic_wd_3_0 := _wd_5_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                              exact (by
                                let _litex_power := _atomic_wd_2_0
                                have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                exact Litex.powStructuralInR _litex_power _recorded_power_base
                              )))
                          intro _litex_input _litex_domain
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                        let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _wd_3_0) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem ((fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _raw_i11) (Litex.denote (Litex.R (M := M))) := (by
                            intro _raw_i11 h_22521 _
                            let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_22521)
                            have h_22521 : Litex.In _value_i11 _wd_3_0 := h_22521
                            have h_22522 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_22521).1
                                  )
                              )
                            have h_22523 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_22521).2.1
                                  )
                              )
                            have h_22524 : Litex.Le _value_i11 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_22521).2.2
                                  )
                              )
                            have h_22525 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_3_0 _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_22521)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                              let _litex_call_arg_1 := _value_i11;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_20380) (by
                                let _atomic_wd_3_1 := _wd_3_0
                                exact h_22521)) True.intro);
                              (Litex.complexAbs _wd_5_0 (by
                                let _atomic_wd_3_0 := _wd_5_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                            exact (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                              let _litex_call_arg_1 := _value_i11;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_20380) (by
                                let _atomic_wd_3_1 := _wd_3_0
                                exact h_22521)) True.intro);
                              (Litex.complexAbs _wd_5_0 (by
                                let _atomic_wd_3_0 := _wd_5_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                              exact (by
                                let _litex_power := _atomic_wd_2_0
                                have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                exact Litex.powStructuralInR _litex_power _recorded_power_base
                              )))
                          intro _litex_input _litex_domain
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
                  (Litex.sqrt _wd_1_0 (by
                    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i10, _raw_i11]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i10, _raw_i11]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i10 h_24336 _
                        let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_24336)
                        have h_24336 : Litex.In _value_i10 _wd_2_0 := h_24336
                        have h_24337 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_24336).1
                              )
                          )
                        have h_24338 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_24336).2.1
                              )
                          )
                        have h_24339 : Litex.Le _value_i10 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_24336).2.2
                              )
                          )
                        have h_24340 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_24336)
                              )
                          )
                        change (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _wd_3_0) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem ((fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _raw_i11) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i11 h_26477 _
                              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_26477)
                              have h_26477 : Litex.In _value_i11 _wd_3_0 := h_26477
                              have h_26478 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_26477).1
                                    )
                                )
                              have h_26479 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_26477).2.1
                                    )
                                )
                              have h_26480 : Litex.Le _value_i11 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_26477).2.2
                                    )
                                )
                              have h_26481 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_3_0 _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_26477)
                                    )
                                )
                              change (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_24336) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_26477)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_24336) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_26477)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_3_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _wd_3_0) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem ((fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _raw_i11) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i11 h_26477 _
                              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_26477)
                              have h_26477 : Litex.In _value_i11 _wd_3_0 := h_26477
                              have h_26478 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_26477).1
                                    )
                                )
                              have h_26479 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_26477).2.1
                                    )
                                )
                              have h_26480 : Litex.Le _value_i11 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_26477).2.2
                                    )
                                )
                              have h_26481 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_3_0 _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_26477)
                                    )
                                )
                              change (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_24336) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_26477)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_24336) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_26477)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_3_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_2_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)) (by
                    let _atomic_wd_1_1 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i10, _raw_i11]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i10, _raw_i11]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i10 h_28377 _
                        let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_28377)
                        have h_28377 : Litex.In _value_i10 _wd_2_0 := h_28377
                        have h_28378 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_28377).1
                              )
                          )
                        have h_28379 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_28377).2.1
                              )
                          )
                        have h_28380 : Litex.Le _value_i10 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_28377).2.2
                              )
                          )
                        have h_28381 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_28377)
                              )
                          )
                        change (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _wd_3_0) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem ((fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _raw_i11) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i11 h_30518 _
                              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_30518)
                              have h_30518 : Litex.In _value_i11 _wd_3_0 := h_30518
                              have h_30519 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_30518).1
                                    )
                                )
                              have h_30520 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_30518).2.1
                                    )
                                )
                              have h_30521 : Litex.Le _value_i11 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_30518).2.2
                                    )
                                )
                              have h_30522 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_3_0 _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_30518)
                                    )
                                )
                              change (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_28377) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_30518)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_28377) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_30518)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_3_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _wd_3_0) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem ((fun (_raw_i11 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), _raw_i11]))) (M.number (2 : ℂ)))) _raw_i11) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i11 h_30518 _
                              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_30518)
                              have h_30518 : Litex.In _value_i11 _wd_3_0 := h_30518
                              have h_30519 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_30518).1
                                    )
                                )
                              have h_30520 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_30518).2.1
                                    )
                                )
                              have h_30521 : Litex.Le _value_i11 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i11 h_30518).2.2
                                    )
                                )
                              have h_30522 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_3_0 _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_30518)
                                    )
                                )
                              change (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_28377) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_30518)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i10;
                                let _litex_call_arg_1 := _value_i11;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_28377) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_30518)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_3_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_2_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i4 h_4246 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_4246)
                        have h_4246 : Litex.In _value_i4 _wd_1_0 := h_4246
                        have h_4247 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).1
                              )
                          )
                        have h_4248 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.1
                              )
                          )
                        have h_4249 : Litex.Le _value_i4 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.2
                              )
                          )
                        have h_4250 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4246)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i5 h_6385 _
                              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                                    )
                                )
                              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                                    )
                                )
                              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                                    )
                                )
                              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_2_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i5 h_6385 _
                              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                                    )
                                )
                              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                                    )
                                )
                              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                                    )
                                )
                              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_2_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                      let _left := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i4 h_4246 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_4246)
                        have h_4246 : Litex.In _value_i4 _wd_1_0 := h_4246
                        have h_4247 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).1
                              )
                          )
                        have h_4248 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.1
                              )
                          )
                        have h_4249 : Litex.Le _value_i4 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.2
                              )
                          )
                        have h_4250 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4246)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i5 h_6385 _
                              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                                    )
                                )
                              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                                    )
                                )
                              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                                    )
                                )
                              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_2_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i5 h_6385 _
                              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                                    )
                                )
                              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                                    )
                                )
                              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                                    )
                                )
                              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_2_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                      let _right := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) h_1))));
                  let _equal_wd_2_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                  let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i6 h_32344 _
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_32344)
                      have h_32344 : Litex.In _value_i6 _wd_2_0 := h_32344
                      have h_32345 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_32344).1
                            )
                        )
                      have h_32346 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_32344).2.1
                            )
                        )
                      have h_32347 : Litex.Le _value_i6 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_32344).2.2
                            )
                        )
                      have h_32348 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_32344)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                        let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
                            intro _raw_i7 h_34485 _
                            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_34485)
                            have h_34485 : Litex.In _value_i7 _wd_3_0 := h_34485
                            have h_34486 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_34485).1
                                  )
                              )
                            have h_34487 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_34485).2.1
                                  )
                              )
                            have h_34488 : Litex.Le _value_i7 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_34485).2.2
                                  )
                              )
                            have h_34489 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_34485)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                              let _litex_call_arg_1 := _value_i7;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_32344) (by
                                let _atomic_wd_3_1 := _wd_3_0
                                exact h_34485)) True.intro);
                              (Litex.complexAbs _wd_5_0 (by
                                let _atomic_wd_3_0 := _wd_5_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                            exact (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                              let _litex_call_arg_1 := _value_i7;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_32344) (by
                                let _atomic_wd_3_1 := _wd_3_0
                                exact h_34485)) True.intro);
                              (Litex.complexAbs _wd_5_0 (by
                                let _atomic_wd_3_0 := _wd_5_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                              exact (by
                                let _litex_power := _atomic_wd_2_0
                                have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                exact Litex.powStructuralInR _litex_power _recorded_power_base
                              )))
                          intro _litex_input _litex_domain
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                        let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
                            intro _raw_i7 h_34485 _
                            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_34485)
                            have h_34485 : Litex.In _value_i7 _wd_3_0 := h_34485
                            have h_34486 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_34485).1
                                  )
                              )
                            have h_34487 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_34485).2.1
                                  )
                              )
                            have h_34488 : Litex.Le _value_i7 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_34485).2.2
                                  )
                              )
                            have h_34489 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_34485)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                              let _litex_call_arg_1 := _value_i7;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_32344) (by
                                let _atomic_wd_3_1 := _wd_3_0
                                exact h_34485)) True.intro);
                              (Litex.complexAbs _wd_5_0 (by
                                let _atomic_wd_3_0 := _wd_5_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                            exact (by
                              let _atomic_wd_2_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                              let _litex_call_arg_1 := _value_i7;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_32344) (by
                                let _atomic_wd_3_1 := _wd_3_0
                                exact h_34485)) True.intro);
                              (Litex.complexAbs _wd_5_0 (by
                                let _atomic_wd_3_0 := _wd_5_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                              (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                let _atomic_wd_3_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                              exact (by
                                let _litex_power := _atomic_wd_2_0
                                have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                exact Litex.powStructuralInR _litex_power _recorded_power_base
                              )))
                          intro _litex_input _litex_domain
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
                  (Litex.sqrt _wd_1_0 (by
                    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i6 h_36300 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_36300)
                        have h_36300 : Litex.In _value_i6 _wd_2_0 := h_36300
                        have h_36301 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_36300).1
                              )
                          )
                        have h_36302 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_36300).2.1
                              )
                          )
                        have h_36303 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_36300).2.2
                              )
                          )
                        have h_36304 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_36300)
                              )
                          )
                        change (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i7 h_38441 _
                              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_38441)
                              have h_38441 : Litex.In _value_i7 _wd_3_0 := h_38441
                              have h_38442 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_38441).1
                                    )
                                )
                              have h_38443 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_38441).2.1
                                    )
                                )
                              have h_38444 : Litex.Le _value_i7 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_38441).2.2
                                    )
                                )
                              have h_38445 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_38441)
                                    )
                                )
                              change (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                                let _litex_call_arg_1 := _value_i7;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_36300) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_38441)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                                let _litex_call_arg_1 := _value_i7;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_36300) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_38441)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_3_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i7 h_38441 _
                              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_38441)
                              have h_38441 : Litex.In _value_i7 _wd_3_0 := h_38441
                              have h_38442 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_38441).1
                                    )
                                )
                              have h_38443 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_38441).2.1
                                    )
                                )
                              have h_38444 : Litex.Le _value_i7 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_38441).2.2
                                    )
                                )
                              have h_38445 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_38441)
                                    )
                                )
                              change (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                                let _litex_call_arg_1 := _value_i7;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_36300) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_38441)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                                let _litex_call_arg_1 := _value_i7;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_36300) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_38441)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_3_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_2_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)) (by
                    let _atomic_wd_1_1 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i7]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i6 h_40341 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_40341)
                        have h_40341 : Litex.In _value_i6 _wd_2_0 := h_40341
                        have h_40342 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_40341).1
                              )
                          )
                        have h_40343 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_40341).2.1
                              )
                          )
                        have h_40344 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_40341).2.2
                              )
                          )
                        have h_40345 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_40341)
                              )
                          )
                        change (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i7 h_42482 _
                              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_42482)
                              have h_42482 : Litex.In _value_i7 _wd_3_0 := h_42482
                              have h_42483 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_42482).1
                                    )
                                )
                              have h_42484 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_42482).2.1
                                    )
                                )
                              have h_42485 : Litex.Le _value_i7 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_42482).2.2
                                    )
                                )
                              have h_42486 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_42482)
                                    )
                                )
                              change (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                                let _litex_call_arg_1 := _value_i7;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_40341) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_42482)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                                let _litex_call_arg_1 := _value_i7;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_40341) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_42482)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_3_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_3_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _wd_3_0) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → M.mem ((fun (_raw_i7 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i7]))) (M.number (2 : ℂ)))) _raw_i7) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i7 h_42482 _
                              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_42482)
                              have h_42482 : Litex.In _value_i7 _wd_3_0 := h_42482
                              have h_42483 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_42482).1
                                    )
                                )
                              have h_42484 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_42482).2.1
                                    )
                                )
                              have h_42485 : Litex.Le _value_i7 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_3_0 _value_i7 h_42482).2.2
                                    )
                                )
                              have h_42486 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_3_0 _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_42482)
                                    )
                                )
                              change (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                                let _litex_call_arg_1 := _value_i7;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_40341) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_42482)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_3_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_3_0 := (let _wd_4_0 := (let _wd_5_0 := (let _litex_call_arg_0 := _value_i6;
                                let _litex_call_arg_1 := _value_i7;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_2_0), (Litex.denote _wd_3_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_2_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_3_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_4_1 := _wd_2_0
                                  exact h_40341) (by
                                  let _atomic_wd_4_1 := _wd_3_0
                                  exact h_42482)) True.intro);
                                (Litex.complexAbs _wd_5_0 (by
                                  let _atomic_wd_4_0 := _wd_5_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_4_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_4_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_4_0 _wd_4_1 (2 : ℕ) (by
                                  let _atomic_wd_4_0 := (let _wd_5_0 := (_wd_4_0).val.arg;
                                  (Litex.complexAbs _wd_5_0 (by
                                    let _atomic_wd_5_0 := _wd_5_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_5_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_4_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_4_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_3_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_3_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_3_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_3_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_3_0 _wd_3_1 _wd_3_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_3_0) (Litex.denote _litex_output) (Litex.isSet _wd_3_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_3_0)) (by
                            let _atomic_wd_3_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_3_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_3_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_2_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i4 h_4246 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_4246)
                        have h_4246 : Litex.In _value_i4 _wd_1_0 := h_4246
                        have h_4247 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).1
                              )
                          )
                        have h_4248 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.1
                              )
                          )
                        have h_4249 : Litex.Le _value_i4 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.2
                              )
                          )
                        have h_4250 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4246)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i5 h_6385 _
                              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                                    )
                                )
                              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                                    )
                                )
                              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                                    )
                                )
                              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_2_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i5 h_6385 _
                              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                                    )
                                )
                              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                                    )
                                )
                              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                                    )
                                )
                              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_2_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                      let _left := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i4, _raw_i5]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i4 h_4246 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_4246)
                        have h_4246 : Litex.In _value_i4 _wd_1_0 := h_4246
                        have h_4247 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).1
                              )
                          )
                        have h_4248 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.1
                              )
                          )
                        have h_4249 : Litex.Le _value_i4 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_4246).2.2
                              )
                          )
                        have h_4250 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4246)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i5 h_6385 _
                              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                                    )
                                )
                              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                                    )
                                )
                              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                                    )
                                )
                              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_2_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _wd_2_0) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), _raw_i5]))) (M.number (2 : ℂ)))) _raw_i5) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i5 h_6385 _
                              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_6385)
                              have h_6385 : Litex.In _value_i5 _wd_2_0 := h_6385
                              have h_6386 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).1
                                    )
                                )
                              have h_6387 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.1
                                    )
                                )
                              have h_6388 : Litex.Le _value_i5 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i5 h_6385).2.2
                                    )
                                )
                              have h_6389 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6385)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                              exact (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                                let _litex_call_arg_1 := _value_i5;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_38 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_4246) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_6385)) True.intro);
                                (Litex.complexAbs _wd_4_0 (by
                                  let _atomic_wd_3_0 := _wd_4_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_3_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                                  let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                                  (Litex.complexAbs _wd_4_0 (by
                                    let _atomic_wd_4_0 := _wd_4_0
                                    exact (by
                                      let _litex_return_call := _atomic_wd_4_0
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                  exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                                exact (by
                                  let _litex_power := _atomic_wd_2_0
                                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                )))
                            intro _litex_input _litex_domain
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_20))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                      let _right := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) h_1))));
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (by
                    let _left := _equal_wd_2_0
                    let _right := _equal_wd_2_1
                    exact (show Litex.Same _left _right from rfl)))))
                  )))
                )
            )
          exact h_2
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_frobenius_x5f_norm_x5f_definition_x2f_statement_x2e_lit
