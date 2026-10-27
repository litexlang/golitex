import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_frobenius_x5f_norm_x5f_nonnegative_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_21 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)), (by
  let _atomic_wd_1_1 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_4 h_6 (by
    let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)
    exact h_21))
  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_6 _Host_i3 _rep_i3 _value_i3 h_21
          have h_5 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_4)
                )
            )
          have h_7 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_6)
                )
            )
          let _object_h22 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)))
          have h_22 : Litex.In _value_i3 _object_h22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6) _object_h22 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6))) h_21)
                )
            )
          have h_96 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have h_98 : Litex.In _value_i2 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_113 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98) :=
            (by
              litex_checked_step =>
                exact (
                  h_21
                )
            )
          have h_97 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_96)
                )
            )
          have h_99 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_98)
                )
            )
          let _object_h114 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)))
          have h_114 : Litex.In _value_i3 _object_h114 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98) _object_h114 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98))) h_113)
                )
            )
          have h_118 : Litex.Same (let _wd_1_0 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_96 h_98 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
            exact h_113));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_96 h_98 (by
              let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
              exact h_113))
            exact (Litex.frobeniusNormInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_96));
          let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_98))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_98))) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i9, _raw_i10]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (Litex.denote _wd_1_0) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → M.mem ((fun (_raw_i9 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_98))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_98))) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i9, _raw_i10]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i9) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i9 h_6241 _
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_6241)
              have h_6241 : Litex.In _value_i9 _wd_1_0 := h_6241
              have h_6242 : Litex.In _value_i9 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_6241).1
                    )
                )
              have h_6243 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i9 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_6241).2.1
                    )
                )
              have h_6244 : Litex.Le _value_i9 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_6241).2.2
                    )
                )
              have h_6245 : Litex.In _value_i9 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_1_0 _value_i9 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6241)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_98));
                let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _litex_input) (by
                  have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                    intro _raw_i10 h_8382 _
                    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_8382)
                    have h_8382 : Litex.In _value_i10 _wd_2_0 := h_8382
                    have h_8383 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_8382).1
                          )
                      )
                    have h_8384 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_8382).2.1
                          )
                      )
                    have h_8385 : Litex.Le _value_i10 _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_8382).2.2
                          )
                      )
                    have h_8386 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_8382)
                          )
                      )
                    change (by
                      let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                      let _litex_call_arg_1 := _value_i10;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                        have _finiteProof_0 := (Litex.isSet _wd_1_0)
                        have _finiteProof_1 := (Litex.isSet _wd_2_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_114 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_6241) (by
                        let _atomic_wd_3_1 := _wd_2_0
                        exact h_8382)) True.intro);
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
                      let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                      let _litex_call_arg_1 := _value_i10;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                        have _finiteProof_0 := (Litex.isSet _wd_1_0)
                        have _finiteProof_1 := (Litex.isSet _wd_2_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_114 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_6241) (by
                        let _atomic_wd_3_1 := _wd_2_0
                        exact h_8382)) True.intro);
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
                  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                  exact _litex_checked_return _litex_input _litex_members _litex_guard));
                (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_98))
                  exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_98))
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_98))
                  exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_98));
                let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _litex_input) (by
                  have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                    intro _raw_i10 h_8382 _
                    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_8382)
                    have h_8382 : Litex.In _value_i10 _wd_2_0 := h_8382
                    have h_8383 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_8382).1
                          )
                      )
                    have h_8384 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_8382).2.1
                          )
                      )
                    have h_8385 : Litex.Le _value_i10 _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_8382).2.2
                          )
                      )
                    have h_8386 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_8382)
                          )
                      )
                    change (by
                      let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                      let _litex_call_arg_1 := _value_i10;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                        have _finiteProof_0 := (Litex.isSet _wd_1_0)
                        have _finiteProof_1 := (Litex.isSet _wd_2_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_114 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_6241) (by
                        let _atomic_wd_3_1 := _wd_2_0
                        exact h_8382)) True.intro);
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
                      let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                      let _litex_call_arg_1 := _value_i10;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                        have _finiteProof_0 := (Litex.isSet _wd_1_0)
                        have _finiteProof_1 := (Litex.isSet _wd_2_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_114 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_6241) (by
                        let _atomic_wd_3_1 := _wd_2_0
                        exact h_8382)) True.intro);
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
                  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                  exact _litex_checked_return _litex_input _litex_members _litex_guard));
                (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_98))
                  exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_98))
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_98))
                  exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_96))
            exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_96))
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_96))
            exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_115 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_96
                          )
                      )
                    have h_124 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_115)
                          )
                      )
                    have h_116 : Litex.In _value_i2 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_98
                          )
                      )
                    have h_133 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i2 h_116)
                          )
                      )
                    have h_117 : (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                      exact Litex.In _value_i3 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                              exact h_113)
                          )
                      )
                    let _object_h146 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)))
                    have h_146 : Litex.In _value_i3 _object_h146 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98) _object_h146 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98))) h_117)
                          )
                      )
                    exact (And.left (And.intro (show (by
                    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_115 h_116 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                      exact h_117));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_115 h_116 (by
                        let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                        exact h_117))
                      exact (Litex.frobeniusNormInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    let _equal_wd_1_1 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i9, _raw_i10]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (Litex.denote _wd_1_0) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → M.mem ((fun (_raw_i9 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i9, _raw_i10]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i9) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i9 h_665 _
                        let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_665)
                        have h_665 : Litex.In _value_i9 _wd_1_0 := h_665
                        have h_666 : Litex.In _value_i9 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_665).1
                              )
                          )
                        have h_667 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i9 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_665).2.1
                              )
                          )
                        have h_668 : Litex.Le _value_i9 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_665).2.2
                              )
                          )
                        have h_669 : Litex.In _value_i9 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i9 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_665)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i10 h_3647 _
                              let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_3647)
                              have h_3647 : Litex.In _value_i10 _wd_2_0 := h_3647
                              have h_3648 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).1
                                    )
                                )
                              have h_3649 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.1
                                    )
                                )
                              have h_3650 : Litex.Le _value_i10 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.2
                                    )
                                )
                              have h_3651 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3647)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                                let _litex_call_arg_1 := _value_i10;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_665) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_3647)) True.intro);
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
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                                let _litex_call_arg_1 := _value_i10;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_665) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_3647)) True.intro);
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
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i10 h_3647 _
                              let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_3647)
                              have h_3647 : Litex.In _value_i10 _wd_2_0 := h_3647
                              have h_3648 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).1
                                    )
                                )
                              have h_3649 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.1
                                    )
                                )
                              have h_3650 : Litex.Le _value_i10 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.2
                                    )
                                )
                              have h_3651 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3647)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                                let _litex_call_arg_1 := _value_i10;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_665) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_3647)) True.intro);
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
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                                let _litex_call_arg_1 := _value_i10;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_665) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_3647)) True.intro);
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
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) from (Litex.frobeniusNormSquare (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_115 h_116 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                    exact h_117))).trans (congrArg M.number (Litex.frobeniusNormSumFormula (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_115 h_116 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                    exact h_117)) ((let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i9, _raw_i10]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (Litex.denote _wd_1_0) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → M.mem ((fun (_raw_i9 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i9, _raw_i10]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i9) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i9 h_665 _
                      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_665)
                      have h_665 : Litex.In _value_i9 _wd_1_0 := h_665
                      have h_666 : Litex.In _value_i9 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_665).1
                            )
                        )
                      have h_667 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i9 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_665).2.1
                            )
                        )
                      have h_668 : Litex.Le _value_i9 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_665).2.2
                            )
                        )
                      have h_669 : Litex.In _value_i9 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i9 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_665)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116));
                        let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                            intro _raw_i10 h_3647 _
                            let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_3647)
                            have h_3647 : Litex.In _value_i10 _wd_2_0 := h_3647
                            have h_3648 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).1
                                  )
                              )
                            have h_3649 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.1
                                  )
                              )
                            have h_3650 : Litex.Le _value_i10 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.2
                                  )
                              )
                            have h_3651 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3647)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                              let _litex_call_arg_1 := _value_i10;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_665) (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_3647)) True.intro);
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
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                              let _litex_call_arg_1 := _value_i10;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_665) (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_3647)) True.intro);
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
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116));
                        let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                            intro _raw_i10 h_3647 _
                            let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_3647)
                            have h_3647 : Litex.In _value_i10 _wd_2_0 := h_3647
                            have h_3648 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).1
                                  )
                              )
                            have h_3649 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.1
                                  )
                              )
                            have h_3650 : Litex.Le _value_i10 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.2
                                  )
                              )
                            have h_3651 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3647)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                              let _litex_call_arg_1 := _value_i10;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_665) (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_3647)) True.intro);
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
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                              let _litex_call_arg_1 := _value_i10;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_665) (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_3647)) True.intro);
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
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))).val.function (by rfl) (by rfl)))) (show (by
                    let _atomic_wd_1_1 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_115 h_116 (by
                      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                      exact h_117))
                    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) from Litex.frobeniusNormNonnegative (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_115 h_116 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                    exact h_117)))))
                  )
                )
            )

          have h_119 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_96 h_98 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
            exact h_113)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_115 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_96
                          )
                      )
                    have h_124 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_115)
                          )
                      )
                    have h_116 : Litex.In _value_i2 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_98
                          )
                      )
                    have h_133 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i2 h_116)
                          )
                      )
                    have h_117 : (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                      exact Litex.In _value_i3 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                              exact h_113)
                          )
                      )
                    let _object_h146 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)))
                    have h_146 : Litex.In _value_i3 _object_h146 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98) _object_h146 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98))) h_117)
                          )
                      )
                    exact (And.right (And.intro (show (by
                    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_115 h_116 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                      exact h_117));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_115 h_116 (by
                        let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                        exact h_117))
                      exact (Litex.frobeniusNormInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    let _equal_wd_1_1 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i9, _raw_i10]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (Litex.denote _wd_1_0) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → M.mem ((fun (_raw_i9 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i9, _raw_i10]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i9) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i9 h_665 _
                        let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_665)
                        have h_665 : Litex.In _value_i9 _wd_1_0 := h_665
                        have h_666 : Litex.In _value_i9 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_665).1
                              )
                          )
                        have h_667 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i9 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_665).2.1
                              )
                          )
                        have h_668 : Litex.Le _value_i9 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_665).2.2
                              )
                          )
                        have h_669 : Litex.In _value_i9 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i9 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_665)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i10 h_3647 _
                              let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_3647)
                              have h_3647 : Litex.In _value_i10 _wd_2_0 := h_3647
                              have h_3648 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).1
                                    )
                                )
                              have h_3649 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.1
                                    )
                                )
                              have h_3650 : Litex.Le _value_i10 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.2
                                    )
                                )
                              have h_3651 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3647)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                                let _litex_call_arg_1 := _value_i10;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_665) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_3647)) True.intro);
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
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                                let _litex_call_arg_1 := _value_i10;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_665) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_3647)) True.intro);
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
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116));
                          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _litex_input) (by
                            have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                              intro _raw_i10 h_3647 _
                              let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_3647)
                              have h_3647 : Litex.In _value_i10 _wd_2_0 := h_3647
                              have h_3648 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).1
                                    )
                                )
                              have h_3649 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.1
                                    )
                                )
                              have h_3650 : Litex.Le _value_i10 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.2
                                    )
                                )
                              have h_3651 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3647)
                                    )
                                )
                              change (by
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                                let _litex_call_arg_1 := _value_i10;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_665) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_3647)) True.intro);
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
                                let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                                let _litex_call_arg_1 := _value_i10;
                                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                  have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                  let _atomic_wd_3_1 := _wd_1_0
                                  exact h_665) (by
                                  let _atomic_wd_3_1 := _wd_2_0
                                  exact h_3647)) True.intro);
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
                            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                            exact _litex_checked_return _litex_input _litex_members _litex_guard));
                          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                            exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                            let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                            let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                            exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                          exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) from (Litex.frobeniusNormSquare (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_115 h_116 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                    exact h_117))).trans (congrArg M.number (Litex.frobeniusNormSumFormula (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_115 h_116 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                    exact h_117)) ((let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i9, _raw_i10]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (Litex.denote _wd_1_0) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → M.mem ((fun (_raw_i9 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i9, _raw_i10]))) (M.number (2 : ℂ)))) _captured_input)) _aggregate_item))))) _raw_i9) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i9 h_665 _
                      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_665)
                      have h_665 : Litex.In _value_i9 _wd_1_0 := h_665
                      have h_666 : Litex.In _value_i9 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_665).1
                            )
                        )
                      have h_667 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i9 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_665).2.1
                            )
                        )
                      have h_668 : Litex.Le _value_i9 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_665).2.2
                            )
                        )
                      have h_669 : Litex.In _value_i9 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i9 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_665)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116));
                        let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                            intro _raw_i10 h_3647 _
                            let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_3647)
                            have h_3647 : Litex.In _value_i10 _wd_2_0 := h_3647
                            have h_3648 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).1
                                  )
                              )
                            have h_3649 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.1
                                  )
                              )
                            have h_3650 : Litex.Le _value_i10 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.2
                                  )
                              )
                            have h_3651 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3647)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                              let _litex_call_arg_1 := _value_i10;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_665) (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_3647)) True.intro);
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
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                              let _litex_call_arg_1 := _value_i10;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_665) (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_3647)) True.intro);
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
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116));
                        let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _wd_2_0) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → M.mem ((fun (_raw_i10 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), _raw_i10]))) (M.number (2 : ℂ)))) _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
                            intro _raw_i10 h_3647 _
                            let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_3647)
                            have h_3647 : Litex.In _value_i10 _wd_2_0 := h_3647
                            have h_3648 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).1
                                  )
                              )
                            have h_3649 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.1
                                  )
                              )
                            have h_3650 : Litex.Le _value_i10 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_2_0 _value_i10 h_3647).2.2
                                  )
                              )
                            have h_3651 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_2_0 _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3647)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                              let _litex_call_arg_1 := _value_i10;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_665) (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_3647)) True.intro);
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
                              let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i9;
                              let _litex_call_arg_1 := _value_i10;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_2_0)] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet _wd_2_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_146 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_665) (by
                                let _atomic_wd_3_1 := _wd_2_0
                                exact h_3647)) True.intro);
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
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_116))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_115))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))).val.function (by rfl) (by rfl)))) (show (by
                    let _atomic_wd_1_1 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_115 h_116 (by
                      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                      exact h_117))
                    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) from Litex.frobeniusNormNonnegative (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_115 h_116 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                    exact h_117)))))
                  )
                )
            )
          have h_3 : (by
            let _atomic_wd_1_1 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_96 h_98 (by
              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
              exact h_113))
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_96 h_98 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
                      exact h_113))
                    exact h_119)
                )
            )
          exact (by
            let _atomic_wd_1_1 := (Litex.frobeniusNorm _value_i3 _value_i1 _value_i2 h_96 h_98 (by
              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_96 h_98)
              exact h_113))
            exact h_119)
        )
      )
  )

theorem h_11187 : (by
  have h_11188 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.N (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))
        )
    )
  have h_11189 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        )
    )
  have h_11190 : (by
    let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_11188 h_11189)
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_11188 h_11189)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_11188 h_11189)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_11188 h_11189)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))
        )
    )
  exact (by
    let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_11188 h_11189);
    let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
    let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
    (Litex.frobeniusNorm _wd_1_0 _wd_1_1 _wd_1_2 h_11188 h_11189 (by
      let _atomic_wd_1_0 := _wd_1_0
      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_11188 h_11189)
      exact h_11190)))
    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_11188 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))
                )
            )
          have h_11192 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (0 : ℂ)) h_11188)
                )
            )
          have h_11189 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                )
            )
          have h_11195 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (2 : ℂ)) h_11189)
                )
            )
          have h_11190 : (by
            let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_11188 h_11189)
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_11188 h_11189)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_11188 h_11189)
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_11188 h_11189)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.zeroMatrixSignature (_litex_matrix).val.rows (_litex_matrix).val.cols); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.zeroMatrixInFnSet _litex_matrix)))))
                )
            )
          let _object_h11229 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_11188 h_11189)))
          have h_11229 : Litex.In (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_11188 h_11189) _object_h11229 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_11188 h_11189) (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_11188 h_11189) (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_11188 h_11189) _object_h11229 (Litex.sameRefl (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_11188 h_11189)) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_11188 h_11189))) h_11190)
                )
            )
          have h_11191 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_11188 h_11189);
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
          (Litex.frobeniusNorm _wd_1_0 _wd_1_1 _wd_1_2 h_11188 h_11189 (by
            let _atomic_wd_1_0 := _wd_1_0
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_11188 h_11189)
            exact h_11190))) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2 (M := M)) (Litex.number (M := M) (0 : ℂ)) h_11188 (Litex.number (M := M) (2 : ℂ)) h_11189 (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_11188 h_11189) h_11190)
                )
            )
          exact (by
          let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.zeroMatrix (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) h_11188 h_11189);
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
          (Litex.frobeniusNorm _wd_1_0 _wd_1_1 _wd_1_2 h_11188 h_11189 (by
            let _atomic_wd_1_0 := _wd_1_0
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_11188 h_11189)
            exact h_11190)))
          exact h_11191)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_frobenius_x5f_norm_x5f_nonnegative_x2f_statement_x2e_lit
