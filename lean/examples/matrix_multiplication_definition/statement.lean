import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_multiplication_x5f_definition_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_23 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_25 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_27 : Litex.In _value_i3 (Litex.N (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_42 : Litex.In _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25)) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_61 : Litex.In _value_i5 (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27)), (by
  let _object_h43 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25)))
  have h_43 : Litex.In _value_i4 _object_h43 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25) _object_h43 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25))) h_42)
        )
    )
  let _object_h62 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27)))
  have h_62 : Litex.In _value_i5 _object_h62 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i5 _value_i5 (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27) _object_h62 (Litex.sameRefl _value_i5) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27))) h_61)
        )
    )
  let _object_w33 := (Litex.matrixMultiply _value_i4 _value_i5 _value_i1 _value_i2 _value_i3 h_23 h_25 h_27 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25)
    exact h_42) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
    exact h_61))
  let _object_w34 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, _raw_i7])))) _captured_input)) _aggregate_item))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
    have _litex_checked_return : ∀ (_raw_i6 : M.Value) (_raw_i7 : M.Value), M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))) → M.mem _raw_i7 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))) → ((fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True) _raw_i6 _raw_i7) → M.mem ((fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, _raw_i7])))) _captured_input)) _aggregate_item))))) _raw_i6 _raw_i7) (Litex.denote (Litex.C (M := M))) := (by
      intro _raw_i6 _raw_i7 h_758 h_763 _
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_758)
      have h_758 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) := h_758
      have h_759 : Litex.In _value_i6 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i6 h_758).1
            )
        )
      have h_760 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i6 h_758).2.1
            )
        )
      have h_761 : Litex.Le _value_i6 _value_i1 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i6 h_758).2.2
            )
        )
      have h_762 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_758)
            )
        )
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_763)
      have h_763 : Litex.In _value_i7 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) := h_763
      have h_764 : Litex.In _value_i7 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i7 h_763).1
            )
        )
      have h_765 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i7 h_763).2.1
            )
        )
      have h_766 : Litex.Le _value_i7 _value_i3 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i7 h_763).2.2
            )
        )
      have h_767 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_763)
            )
        )
      change (by
        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25));
        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _litex_input) (by
          have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote _wd_1_0) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _raw_i8) (Litex.denote (Litex.C (M := M))) := (by
            intro _raw_i8 h_4210 _
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4210)
            have h_4210 : Litex.In _value_i8 _wd_1_0 := h_4210
            have h_4211 : Litex.In _value_i8 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4210).1
                  )
              )
            have h_4212 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i8 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4210).2.1
                  )
              )
            have h_4213 : Litex.Le _value_i8 _value_i2 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4210).2.2
                  )
              )
            have h_4214 : Litex.In _value_i8 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive _wd_1_0 _value_i8 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4210)
                  )
              )
            change (by
              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
              let _litex_call_arg_1 := _value_i8;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                exact h_758) (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_4210)) True.intro);
              let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
              let _litex_call_arg_1 := _value_i7;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_4210) (by
                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                exact h_763)) True.intro);
              (Litex.mul _wd_2_0 _wd_2_1 (by
                let _atomic_wd_3_0 := _wd_2_0
                exact (by
                  let _litex_return_call := _atomic_wd_3_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                let _atomic_wd_3_0 := _wd_2_1
                exact (by
                  let _litex_return_call := _atomic_wd_3_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
              exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
            exact (by
              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
              let _litex_call_arg_1 := _value_i8;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                exact h_758) (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_4210)) True.intro);
              let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
              let _litex_call_arg_1 := _value_i7;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_4210) (by
                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                exact h_763)) True.intro);
              (Litex.mul _wd_2_0 _wd_2_1 (by
                let _atomic_wd_3_0 := _wd_2_0
                exact (by
                  let _litex_return_call := _atomic_wd_3_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                let _atomic_wd_3_0 := _wd_2_1
                exact (by
                  let _litex_return_call := _atomic_wd_3_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
              exact (by
                let _arithmetic := _atomic_wd_2_0
                exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
          intro _litex_input _litex_domain
          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
          exact _litex_checked_return _litex_input _litex_members _litex_guard));
        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (by
          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
      exact (by
        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25));
        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _litex_input) (by
          have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote _wd_1_0) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _raw_i8) (Litex.denote (Litex.C (M := M))) := (by
            intro _raw_i8 h_4210 _
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4210)
            have h_4210 : Litex.In _value_i8 _wd_1_0 := h_4210
            have h_4211 : Litex.In _value_i8 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4210).1
                  )
              )
            have h_4212 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i8 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4210).2.1
                  )
              )
            have h_4213 : Litex.Le _value_i8 _value_i2 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4210).2.2
                  )
              )
            have h_4214 : Litex.In _value_i8 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive _wd_1_0 _value_i8 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4210)
                  )
              )
            change (by
              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
              let _litex_call_arg_1 := _value_i8;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                exact h_758) (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_4210)) True.intro);
              let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
              let _litex_call_arg_1 := _value_i7;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_4210) (by
                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                exact h_763)) True.intro);
              (Litex.mul _wd_2_0 _wd_2_1 (by
                let _atomic_wd_3_0 := _wd_2_0
                exact (by
                  let _litex_return_call := _atomic_wd_3_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                let _atomic_wd_3_0 := _wd_2_1
                exact (by
                  let _litex_return_call := _atomic_wd_3_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
              exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
            exact (by
              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
              let _litex_call_arg_1 := _value_i8;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                exact h_758) (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_4210)) True.intro);
              let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
              let _litex_call_arg_1 := _value_i7;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_4210) (by
                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                exact h_763)) True.intro);
              (Litex.mul _wd_2_0 _wd_2_1 (by
                let _atomic_wd_3_0 := _wd_2_0
                exact (by
                  let _litex_return_call := _atomic_wd_3_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                let _atomic_wd_3_0 := _wd_2_1
                exact (by
                  let _litex_return_call := _atomic_wd_3_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
              exact (by
                let _arithmetic := _atomic_wd_2_0
                exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
          intro _litex_input _litex_domain
          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
          exact _litex_checked_return _litex_input _litex_members _litex_guard));
        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (by
          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .complex rfl)))
    intro _litex_input _litex_domain
    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
    exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
  exact (by
    let _equal_wd_1_0 := _object_w33
    let _equal_wd_1_1 := _object_w34
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_23 _Host_i2 _rep_i2 _value_i2 h_25 _Host_i3 _rep_i3 _value_i3 h_27 _Host_i4 _rep_i4 _value_i4 h_42 _Host_i5 _rep_i5 _value_i5 h_61
          have h_24 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_23)
                )
            )
          have h_26 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_25)
                )
            )
          have h_28 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i3 h_27)
                )
            )
          let _object_h43 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25)))
          have h_43 : Litex.In _value_i4 _object_h43 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25) _object_h43 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25))) h_42)
                )
            )
          let _object_h62 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27)))
          have h_62 : Litex.In _value_i5 _object_h62 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i5 _value_i5 (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27) _object_h62 (Litex.sameRefl _value_i5) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27))) h_61)
                )
            )
          let _object_w33 := (Litex.matrixMultiply _value_i4 _value_i5 _value_i1 _value_i2 _value_i3 h_23 h_25 h_27 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25)
            exact h_42) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
            exact h_61))
          let _object_w34 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, _raw_i7])))) _captured_input)) _aggregate_item))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
            have _litex_checked_return : ∀ (_raw_i6 : M.Value) (_raw_i7 : M.Value), M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))) → M.mem _raw_i7 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))) → ((fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True) _raw_i6 _raw_i7) → M.mem ((fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, _raw_i7])))) _captured_input)) _aggregate_item))))) _raw_i6 _raw_i7) (Litex.denote (Litex.C (M := M))) := (by
              intro _raw_i6 _raw_i7 h_758 h_763 _
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_758)
              have h_758 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) := h_758
              have h_759 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i6 h_758).1
                    )
                )
              have h_760 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i6 h_758).2.1
                    )
                )
              have h_761 : Litex.Le _value_i6 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i6 h_758).2.2
                    )
                )
              have h_762 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_758)
                    )
                )
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_763)
              have h_763 : Litex.In _value_i7 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) := h_763
              have h_764 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i7 h_763).1
                    )
                )
              have h_765 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i7 h_763).2.1
                    )
                )
              have h_766 : Litex.Le _value_i7 _value_i3 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i7 h_763).2.2
                    )
                )
              have h_767 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_763)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25));
                let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _litex_input) (by
                  have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote _wd_1_0) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _raw_i8) (Litex.denote (Litex.C (M := M))) := (by
                    intro _raw_i8 h_4210 _
                    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4210)
                    have h_4210 : Litex.In _value_i8 _wd_1_0 := h_4210
                    have h_4211 : Litex.In _value_i8 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4210).1
                          )
                      )
                    have h_4212 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i8 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4210).2.1
                          )
                      )
                    have h_4213 : Litex.Le _value_i8 _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4210).2.2
                          )
                      )
                    have h_4214 : Litex.In _value_i8 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive _wd_1_0 _value_i8 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4210)
                          )
                      )
                    change (by
                      let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                      let _litex_call_arg_1 := _value_i8;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                        have _finiteProof_1 := (Litex.isSet _wd_1_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                        exact h_758) (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_4210)) True.intro);
                      let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
                      let _litex_call_arg_1 := _value_i7;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                        have _finiteProof_0 := (Litex.isSet _wd_1_0)
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_4210) (by
                        let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                        exact h_763)) True.intro);
                      (Litex.mul _wd_2_0 _wd_2_1 (by
                        let _atomic_wd_3_0 := _wd_2_0
                        exact (by
                          let _litex_return_call := _atomic_wd_3_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                        let _atomic_wd_3_0 := _wd_2_1
                        exact (by
                          let _litex_return_call := _atomic_wd_3_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                      exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
                    exact (by
                      let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                      let _litex_call_arg_1 := _value_i8;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                        have _finiteProof_1 := (Litex.isSet _wd_1_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                        exact h_758) (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_4210)) True.intro);
                      let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
                      let _litex_call_arg_1 := _value_i7;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                        have _finiteProof_0 := (Litex.isSet _wd_1_0)
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_4210) (by
                        let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                        exact h_763)) True.intro);
                      (Litex.mul _wd_2_0 _wd_2_1 (by
                        let _atomic_wd_3_0 := _wd_2_0
                        exact (by
                          let _litex_return_call := _atomic_wd_3_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                        let _atomic_wd_3_0 := _wd_2_1
                        exact (by
                          let _litex_return_call := _atomic_wd_3_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                      exact (by
                        let _arithmetic := _atomic_wd_2_0
                        exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                  intro _litex_input _litex_domain
                  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                  exact _litex_checked_return _litex_input _litex_members _litex_guard));
                (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                  exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                  exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25));
                let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _litex_input) (by
                  have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote _wd_1_0) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _raw_i8) (Litex.denote (Litex.C (M := M))) := (by
                    intro _raw_i8 h_4210 _
                    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4210)
                    have h_4210 : Litex.In _value_i8 _wd_1_0 := h_4210
                    have h_4211 : Litex.In _value_i8 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4210).1
                          )
                      )
                    have h_4212 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i8 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4210).2.1
                          )
                      )
                    have h_4213 : Litex.Le _value_i8 _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4210).2.2
                          )
                      )
                    have h_4214 : Litex.In _value_i8 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive _wd_1_0 _value_i8 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4210)
                          )
                      )
                    change (by
                      let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                      let _litex_call_arg_1 := _value_i8;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                        have _finiteProof_1 := (Litex.isSet _wd_1_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                        exact h_758) (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_4210)) True.intro);
                      let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
                      let _litex_call_arg_1 := _value_i7;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                        have _finiteProof_0 := (Litex.isSet _wd_1_0)
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_4210) (by
                        let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                        exact h_763)) True.intro);
                      (Litex.mul _wd_2_0 _wd_2_1 (by
                        let _atomic_wd_3_0 := _wd_2_0
                        exact (by
                          let _litex_return_call := _atomic_wd_3_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                        let _atomic_wd_3_0 := _wd_2_1
                        exact (by
                          let _litex_return_call := _atomic_wd_3_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                      exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
                    exact (by
                      let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                      let _litex_call_arg_1 := _value_i8;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                        have _finiteProof_1 := (Litex.isSet _wd_1_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                        exact h_758) (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_4210)) True.intro);
                      let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
                      let _litex_call_arg_1 := _value_i7;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                        have _finiteProof_0 := (Litex.isSet _wd_1_0)
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_4210) (by
                        let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                        exact h_763)) True.intro);
                      (Litex.mul _wd_2_0 _wd_2_1 (by
                        let _atomic_wd_3_0 := _wd_2_0
                        exact (by
                          let _litex_return_call := _atomic_wd_3_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                        let _atomic_wd_3_0 := _wd_2_1
                        exact (by
                          let _litex_return_call := _atomic_wd_3_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                      exact (by
                        let _arithmetic := _atomic_wd_2_0
                        exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                  intro _litex_input _litex_domain
                  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                  exact _litex_checked_return _litex_input _litex_members _litex_guard));
                (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                  exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                  exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .complex rfl)))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
            exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w33
            let _equal_wd_1_1 := _object_w34
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w33;
                  let _equal_wd_1_1 := _object_w34;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixMultiply_eq_formula _equal_wd_1_0 (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun (_captured_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i17 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i15, _raw_i17])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i17, _raw_i16])))) _captured_input)) _aggregate_item))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                    have _litex_checked_return : ∀ (_raw_i15 : M.Value) (_raw_i16 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))) → M.mem _raw_i16 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))) → ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) _raw_i15 _raw_i16) → M.mem ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun (_captured_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i17 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i15, _raw_i17])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i17, _raw_i16])))) _captured_input)) _aggregate_item))))) _raw_i15 _raw_i16) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i15 _raw_i16 h_7493 h_7498 _
                      let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_7493)
                      have h_7493 : Litex.In _value_i15 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) := h_7493
                      have h_7494 : Litex.In _value_i15 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i15 h_7493).1
                            )
                        )
                      have h_7495 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i15 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i15 h_7493).2.1
                            )
                        )
                      have h_7496 : Litex.Le _value_i15 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i15 h_7493).2.2
                            )
                        )
                      have h_7497 : Litex.In _value_i15 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i15 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_7493)
                            )
                        )
                      let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_7498)
                      have h_7498 : Litex.In _value_i16 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) := h_7498
                      have h_7499 : Litex.In _value_i16 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i16 h_7498).1
                            )
                        )
                      have h_7500 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i16 h_7498).2.1
                            )
                        )
                      have h_7501 : Litex.Le _value_i16 _value_i3 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i16 h_7498).2.2
                            )
                        )
                      have h_7502 : Litex.In _value_i16 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i16 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_7498)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25));
                        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i15), _raw_i17])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i17, (Litex.denote _value_i16)])))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i17 : M.Value), M.mem _raw_i17 (Litex.denote _wd_1_0) → ((fun (_raw_i17 : M.Value) => True) _raw_i17) → M.mem ((fun (_raw_i17 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i15), _raw_i17])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i17, (Litex.denote _value_i16)])))) _raw_i17) (Litex.denote (Litex.C (M := M))) := (by
                            intro _raw_i17 h_10943 _
                            let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_10943)
                            have h_10943 : Litex.In _value_i17 _wd_1_0 := h_10943
                            have h_10944 : Litex.In _value_i17 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i17 h_10943).1
                                  )
                              )
                            have h_10945 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i17 h_10943).2.1
                                  )
                              )
                            have h_10946 : Litex.Le _value_i17 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i17 h_10943).2.2
                                  )
                              )
                            have h_10947 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_1_0 _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_10943)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i15;
                              let _litex_call_arg_1 := _value_i17;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                                exact h_7493) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i17;
                              let _litex_call_arg_1 := _value_i16;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943) (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                                exact h_7498)) True.intro);
                              (Litex.mul _wd_2_0 _wd_2_1 (by
                                let _atomic_wd_3_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_3_0 := _wd_2_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                              exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
                            exact (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i15;
                              let _litex_call_arg_1 := _value_i17;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                                exact h_7493) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i17;
                              let _litex_call_arg_1 := _value_i16;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943) (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                                exact h_7498)) True.intro);
                              (Litex.mul _wd_2_0 _wd_2_1 (by
                                let _atomic_wd_3_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_3_0 := _wd_2_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                              exact (by
                                let _arithmetic := _atomic_wd_2_0
                                exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                          intro _litex_input _litex_domain
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25));
                        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i15), _raw_i17])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i17, (Litex.denote _value_i16)])))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i17 : M.Value), M.mem _raw_i17 (Litex.denote _wd_1_0) → ((fun (_raw_i17 : M.Value) => True) _raw_i17) → M.mem ((fun (_raw_i17 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i15), _raw_i17])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i17, (Litex.denote _value_i16)])))) _raw_i17) (Litex.denote (Litex.C (M := M))) := (by
                            intro _raw_i17 h_10943 _
                            let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_10943)
                            have h_10943 : Litex.In _value_i17 _wd_1_0 := h_10943
                            have h_10944 : Litex.In _value_i17 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i17 h_10943).1
                                  )
                              )
                            have h_10945 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i17 h_10943).2.1
                                  )
                              )
                            have h_10946 : Litex.Le _value_i17 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i17 h_10943).2.2
                                  )
                              )
                            have h_10947 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_1_0 _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_10943)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i15;
                              let _litex_call_arg_1 := _value_i17;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                                exact h_7493) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i17;
                              let _litex_call_arg_1 := _value_i16;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943) (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                                exact h_7498)) True.intro);
                              (Litex.mul _wd_2_0 _wd_2_1 (by
                                let _atomic_wd_3_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_3_0 := _wd_2_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                              exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
                            exact (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i15;
                              let _litex_call_arg_1 := _value_i17;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                                exact h_7493) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i17;
                              let _litex_call_arg_1 := _value_i16;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943) (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                                exact h_7498)) True.intro);
                              (Litex.mul _wd_2_0 _wd_2_1 (by
                                let _atomic_wd_3_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_3_0 := _wd_2_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                              exact (by
                                let _arithmetic := _atomic_wd_2_0
                                exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                          intro _litex_input _litex_domain
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .complex rfl)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                    exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard)) (by rfl) (by rfl))).trans (let _equal_wd_2_0 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun (_captured_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i17 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i15, _raw_i17])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i17, _raw_i16])))) _captured_input)) _aggregate_item))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                    have _litex_checked_return : ∀ (_raw_i15 : M.Value) (_raw_i16 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))) → M.mem _raw_i16 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))) → ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) _raw_i15 _raw_i16) → M.mem ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun (_captured_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i17 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i15, _raw_i17])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i17, _raw_i16])))) _captured_input)) _aggregate_item))))) _raw_i15 _raw_i16) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i15 _raw_i16 h_7493 h_7498 _
                      let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_7493)
                      have h_7493 : Litex.In _value_i15 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) := h_7493
                      have h_7494 : Litex.In _value_i15 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i15 h_7493).1
                            )
                        )
                      have h_7495 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i15 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i15 h_7493).2.1
                            )
                        )
                      have h_7496 : Litex.Le _value_i15 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i15 h_7493).2.2
                            )
                        )
                      have h_7497 : Litex.In _value_i15 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i15 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_7493)
                            )
                        )
                      let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_7498)
                      have h_7498 : Litex.In _value_i16 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) := h_7498
                      have h_7499 : Litex.In _value_i16 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i16 h_7498).1
                            )
                        )
                      have h_7500 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i16 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i16 h_7498).2.1
                            )
                        )
                      have h_7501 : Litex.Le _value_i16 _value_i3 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i16 h_7498).2.2
                            )
                        )
                      have h_7502 : Litex.In _value_i16 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i16 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_7498)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25));
                        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i15), _raw_i17])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i17, (Litex.denote _value_i16)])))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i17 : M.Value), M.mem _raw_i17 (Litex.denote _wd_1_0) → ((fun (_raw_i17 : M.Value) => True) _raw_i17) → M.mem ((fun (_raw_i17 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i15), _raw_i17])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i17, (Litex.denote _value_i16)])))) _raw_i17) (Litex.denote (Litex.C (M := M))) := (by
                            intro _raw_i17 h_10943 _
                            let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_10943)
                            have h_10943 : Litex.In _value_i17 _wd_1_0 := h_10943
                            have h_10944 : Litex.In _value_i17 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i17 h_10943).1
                                  )
                              )
                            have h_10945 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i17 h_10943).2.1
                                  )
                              )
                            have h_10946 : Litex.Le _value_i17 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i17 h_10943).2.2
                                  )
                              )
                            have h_10947 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_1_0 _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_10943)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i15;
                              let _litex_call_arg_1 := _value_i17;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                                exact h_7493) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i17;
                              let _litex_call_arg_1 := _value_i16;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943) (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                                exact h_7498)) True.intro);
                              (Litex.mul _wd_2_0 _wd_2_1 (by
                                let _atomic_wd_3_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_3_0 := _wd_2_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                              exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
                            exact (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i15;
                              let _litex_call_arg_1 := _value_i17;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                                exact h_7493) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i17;
                              let _litex_call_arg_1 := _value_i16;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943) (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                                exact h_7498)) True.intro);
                              (Litex.mul _wd_2_0 _wd_2_1 (by
                                let _atomic_wd_3_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_3_0 := _wd_2_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                              exact (by
                                let _arithmetic := _atomic_wd_2_0
                                exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                          intro _litex_input _litex_domain
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25));
                        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i15), _raw_i17])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i17, (Litex.denote _value_i16)])))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i17 : M.Value), M.mem _raw_i17 (Litex.denote _wd_1_0) → ((fun (_raw_i17 : M.Value) => True) _raw_i17) → M.mem ((fun (_raw_i17 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i15), _raw_i17])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i17, (Litex.denote _value_i16)])))) _raw_i17) (Litex.denote (Litex.C (M := M))) := (by
                            intro _raw_i17 h_10943 _
                            let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_10943)
                            have h_10943 : Litex.In _value_i17 _wd_1_0 := h_10943
                            have h_10944 : Litex.In _value_i17 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i17 h_10943).1
                                  )
                              )
                            have h_10945 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i17 h_10943).2.1
                                  )
                              )
                            have h_10946 : Litex.Le _value_i17 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i17 h_10943).2.2
                                  )
                              )
                            have h_10947 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_1_0 _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_10943)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i15;
                              let _litex_call_arg_1 := _value_i17;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                                exact h_7493) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i17;
                              let _litex_call_arg_1 := _value_i16;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943) (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                                exact h_7498)) True.intro);
                              (Litex.mul _wd_2_0 _wd_2_1 (by
                                let _atomic_wd_3_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_3_0 := _wd_2_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                              exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
                            exact (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i15;
                              let _litex_call_arg_1 := _value_i17;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                                exact h_7493) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i17;
                              let _litex_call_arg_1 := _value_i16;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_10943) (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                                exact h_7498)) True.intro);
                              (Litex.mul _wd_2_0 _wd_2_1 (by
                                let _atomic_wd_3_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_3_0 := _wd_2_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                              exact (by
                                let _arithmetic := _atomic_wd_2_0
                                exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                          intro _litex_input _litex_domain
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .complex rfl)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                    exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard));
                  let _equal_wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, _raw_i7])))) _captured_input)) _aggregate_item))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
                    have _litex_checked_return : ∀ (_raw_i6 : M.Value) (_raw_i7 : M.Value), M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))) → M.mem _raw_i7 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))) → ((fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True) _raw_i6 _raw_i7) → M.mem ((fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i6, _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, _raw_i7])))) _captured_input)) _aggregate_item))))) _raw_i6 _raw_i7) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i6 _raw_i7 h_13985 h_13990 _
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_13985)
                      have h_13985 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) := h_13985
                      have h_13986 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i6 h_13985).1
                            )
                        )
                      have h_13987 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i6 h_13985).2.1
                            )
                        )
                      have h_13988 : Litex.Le _value_i6 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i6 h_13985).2.2
                            )
                        )
                      have h_13989 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_13985)
                            )
                        )
                      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_13990)
                      have h_13990 : Litex.In _value_i7 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) := h_13990
                      have h_13991 : Litex.In _value_i7 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i7 h_13990).1
                            )
                        )
                      have h_13992 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i7 h_13990).2.1
                            )
                        )
                      have h_13993 : Litex.Le _value_i7 _value_i3 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i7 h_13990).2.2
                            )
                        )
                      have h_13994 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_13990)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25));
                        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote _wd_1_0) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _raw_i8) (Litex.denote (Litex.C (M := M))) := (by
                            intro _raw_i8 h_17435 _
                            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_17435)
                            have h_17435 : Litex.In _value_i8 _wd_1_0 := h_17435
                            have h_17436 : Litex.In _value_i8 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_17435).1
                                  )
                              )
                            have h_17437 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i8 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_17435).2.1
                                  )
                              )
                            have h_17438 : Litex.Le _value_i8 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_17435).2.2
                                  )
                              )
                            have h_17439 : Litex.In _value_i8 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_1_0 _value_i8 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_17435)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                              let _litex_call_arg_1 := _value_i8;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                                exact h_13985) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_17435)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
                              let _litex_call_arg_1 := _value_i7;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_17435) (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                                exact h_13990)) True.intro);
                              (Litex.mul _wd_2_0 _wd_2_1 (by
                                let _atomic_wd_3_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_3_0 := _wd_2_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                              exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
                            exact (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                              let _litex_call_arg_1 := _value_i8;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                                exact h_13985) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_17435)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
                              let _litex_call_arg_1 := _value_i7;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_17435) (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                                exact h_13990)) True.intro);
                              (Litex.mul _wd_2_0 _wd_2_1 (by
                                let _atomic_wd_3_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_3_0 := _wd_2_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                              exact (by
                                let _arithmetic := _atomic_wd_2_0
                                exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                          intro _litex_input _litex_domain
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25));
                        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote _wd_1_0) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _raw_i8) (Litex.denote (Litex.C (M := M))) := (by
                            intro _raw_i8 h_17435 _
                            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_17435)
                            have h_17435 : Litex.In _value_i8 _wd_1_0 := h_17435
                            have h_17436 : Litex.In _value_i8 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_17435).1
                                  )
                              )
                            have h_17437 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i8 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_17435).2.1
                                  )
                              )
                            have h_17438 : Litex.Le _value_i8 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_17435).2.2
                                  )
                              )
                            have h_17439 : Litex.In _value_i8 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_1_0 _value_i8 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_17435)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                              let _litex_call_arg_1 := _value_i8;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                                exact h_13985) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_17435)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
                              let _litex_call_arg_1 := _value_i7;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_17435) (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                                exact h_13990)) True.intro);
                              (Litex.mul _wd_2_0 _wd_2_1 (by
                                let _atomic_wd_3_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_3_0 := _wd_2_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                              exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
                            exact (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                              let _litex_call_arg_1 := _value_i8;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))
                                exact h_13985) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_17435)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
                              let _litex_call_arg_1 := _value_i7;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                                have _finiteProof_0 := (Litex.isSet _wd_1_0)
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_62 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_17435) (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27))
                                exact h_13990)) True.intro);
                              (Litex.mul _wd_2_0 _wd_2_1 (by
                                let _atomic_wd_3_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_3_0 := _wd_2_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_3_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                              exact (by
                                let _arithmetic := _atomic_wd_2_0
                                exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                          intro _litex_input _litex_domain
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_25))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .complex rfl)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_23)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_27)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
                    exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard));
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (by
                    let _left : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_0
                    let _right : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_1
                    exact (show Litex.Same _left _right from rfl)))))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_multiplication_x5f_definition_x2f_statement_x2e_lit
