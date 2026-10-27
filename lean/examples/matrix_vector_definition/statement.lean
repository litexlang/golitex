import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_vector_x5f_definition_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_22 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_24 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_39 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24)) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_49 : Litex.In _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24)), (by
  let _object_h40 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24)))
  have h_40 : Litex.In _value_i3 _object_h40 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24) _object_h40 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24))) h_39)
        )
    )
  let _object_h50 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24)))
  have h_50 : Litex.In _value_i4 _object_h50 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i4 _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24) _object_h50 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24)) h_49)
        )
    )
  let _object_w30 := (Litex.matrixApply _value_i3 _value_i4 _value_i1 _value_i2 h_22 h_24 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24)
    exact h_39) (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24)
    exact h_49))
  let _object_w31 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i5, _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _captured_input)) _aggregate_item))))) _litex_input) (by
    have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i5, _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _captured_input)) _aggregate_item))))) _raw_i5) (Litex.denote (Litex.C (M := M))) := (by
      intro _raw_i5 h_366 _
      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_366)
      have h_366 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) := h_366
      have h_367 : Litex.In _value_i5 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i5 h_366).1
            )
        )
      have h_368 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i5 h_366).2.1
            )
        )
      have h_369 : Litex.Le _value_i5 _value_i1 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i5 h_366).2.2
            )
        )
      have h_370 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_366)
            )
        )
      change (by
        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24));
        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _litex_input) (by
          have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
            intro _raw_i6 h_2894 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_2894)
            have h_2894 : Litex.In _value_i6 _wd_1_0 := h_2894
            have h_2895 : Litex.In _value_i6 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2894).1
                  )
              )
            have h_2896 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2894).2.1
                  )
              )
            have h_2897 : Litex.Le _value_i6 _value_i2 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2894).2.2
                  )
              )
            have h_2898 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2894)
                  )
              )
            change (by
              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
              let _litex_call_arg_1 := _value_i6;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                exact h_366) (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_2894)) True.intro);
              let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_2894) True.intro);
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
              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
              let _litex_call_arg_1 := _value_i6;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                exact h_366) (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_2894)) True.intro);
              let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_2894) True.intro);
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
          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
          exact _litex_checked_return _litex_input _litex_members _litex_guard));
        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
      exact (by
        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24));
        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _litex_input) (by
          have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
            intro _raw_i6 h_2894 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_2894)
            have h_2894 : Litex.In _value_i6 _wd_1_0 := h_2894
            have h_2895 : Litex.In _value_i6 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2894).1
                  )
              )
            have h_2896 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2894).2.1
                  )
              )
            have h_2897 : Litex.Le _value_i6 _value_i2 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2894).2.2
                  )
              )
            have h_2898 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2894)
                  )
              )
            change (by
              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
              let _litex_call_arg_1 := _value_i6;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                exact h_366) (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_2894)) True.intro);
              let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_2894) True.intro);
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
              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
              let _litex_call_arg_1 := _value_i6;
              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                exact h_366) (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_2894)) True.intro);
              let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                let _atomic_wd_3_1 := _wd_1_0
                exact h_2894) True.intro);
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
          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
          exact _litex_checked_return _litex_input _litex_members _litex_guard));
        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .complex rfl)))
    intro _litex_input _litex_domain
    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.denote (Litex.C (M := M))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
    exact _litex_checked_return _litex_input _litex_members _litex_guard))
  exact (by
    let _equal_wd_1_0 := _object_w30
    let _equal_wd_1_1 := _object_w31
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_22 _Host_i2 _rep_i2 _value_i2 h_24 _Host_i3 _rep_i3 _value_i3 h_39 _Host_i4 _rep_i4 _value_i4 h_49
          have h_23 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_22)
                )
            )
          have h_25 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_24)
                )
            )
          let _object_h40 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24)))
          have h_40 : Litex.In _value_i3 _object_h40 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24) _object_h40 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24))) h_39)
                )
            )
          let _object_h50 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24)))
          have h_50 : Litex.In _value_i4 _object_h50 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24) _object_h50 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24)) h_49)
                )
            )
          let _object_w30 := (Litex.matrixApply _value_i3 _value_i4 _value_i1 _value_i2 h_22 h_24 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24)
            exact h_39) (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24)
            exact h_49))
          let _object_w31 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i5, _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _captured_input)) _aggregate_item))))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i5, _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _captured_input)) _aggregate_item))))) _raw_i5) (Litex.denote (Litex.C (M := M))) := (by
              intro _raw_i5 h_366 _
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_366)
              have h_366 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) := h_366
              have h_367 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i5 h_366).1
                    )
                )
              have h_368 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i5 h_366).2.1
                    )
                )
              have h_369 : Litex.Le _value_i5 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i5 h_366).2.2
                    )
                )
              have h_370 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_366)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24));
                let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _litex_input) (by
                  have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
                    intro _raw_i6 h_2894 _
                    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_2894)
                    have h_2894 : Litex.In _value_i6 _wd_1_0 := h_2894
                    have h_2895 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2894).1
                          )
                      )
                    have h_2896 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2894).2.1
                          )
                      )
                    have h_2897 : Litex.Le _value_i6 _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2894).2.2
                          )
                      )
                    have h_2898 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2894)
                          )
                      )
                    change (by
                      let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                      let _litex_call_arg_1 := _value_i6;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                        have _finiteProof_1 := (Litex.isSet _wd_1_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                        exact h_366) (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_2894)) True.intro);
                      let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
                      Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_2894) True.intro);
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
                      let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                      let _litex_call_arg_1 := _value_i6;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                        have _finiteProof_1 := (Litex.isSet _wd_1_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                        exact h_366) (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_2894)) True.intro);
                      let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
                      Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_2894) True.intro);
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
                  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                  exact _litex_checked_return _litex_input _litex_members _litex_guard));
                (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                  exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                  exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24));
                let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _litex_input) (by
                  have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
                    intro _raw_i6 h_2894 _
                    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_2894)
                    have h_2894 : Litex.In _value_i6 _wd_1_0 := h_2894
                    have h_2895 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2894).1
                          )
                      )
                    have h_2896 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2894).2.1
                          )
                      )
                    have h_2897 : Litex.Le _value_i6 _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2894).2.2
                          )
                      )
                    have h_2898 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2894)
                          )
                      )
                    change (by
                      let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                      let _litex_call_arg_1 := _value_i6;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                        have _finiteProof_1 := (Litex.isSet _wd_1_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                        exact h_366) (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_2894)) True.intro);
                      let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
                      Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_2894) True.intro);
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
                      let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                      let _litex_call_arg_1 := _value_i6;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                        have _finiteProof_1 := (Litex.isSet _wd_1_0)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                        exact h_366) (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_2894)) True.intro);
                      let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
                      Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                        let _atomic_wd_3_1 := _wd_1_0
                        exact h_2894) True.intro);
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
                  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                  exact _litex_checked_return _litex_input _litex_members _litex_guard));
                (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                  exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                  let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                  exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .complex rfl)))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.denote (Litex.C (M := M))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w30
            let _equal_wd_1_1 := _object_w31
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w30;
                  let _equal_wd_1_1 := _object_w31;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixApply_eq_formula _equal_wd_1_0 (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun (_captured_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i13 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i12, _raw_i13])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i13))) _captured_input)) _aggregate_item))))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) → ((fun (_raw_i12 : M.Value) => True) _raw_i12) → M.mem ((fun (_raw_i12 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun (_captured_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i13 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i12, _raw_i13])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i13))) _captured_input)) _aggregate_item))))) _raw_i12) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i12 h_5145 _
                      let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_5145)
                      have h_5145 : Litex.In _value_i12 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) := h_5145
                      have h_5146 : Litex.In _value_i12 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i12 h_5145).1
                            )
                        )
                      have h_5147 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i12 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i12 h_5145).2.1
                            )
                        )
                      have h_5148 : Litex.Le _value_i12 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i12 h_5145).2.2
                            )
                        )
                      have h_5149 : Litex.In _value_i12 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i12 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5145)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24));
                        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), _raw_i13])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i13))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i13 : M.Value), M.mem _raw_i13 (Litex.denote _wd_1_0) → ((fun (_raw_i13 : M.Value) => True) _raw_i13) → M.mem ((fun (_raw_i13 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), _raw_i13])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i13))) _raw_i13) (Litex.denote (Litex.C (M := M))) := (by
                            intro _raw_i13 h_7671 _
                            let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_7671)
                            have h_7671 : Litex.In _value_i13 _wd_1_0 := h_7671
                            have h_7672 : Litex.In _value_i13 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i13 h_7671).1
                                  )
                              )
                            have h_7673 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i13 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i13 h_7671).2.1
                                  )
                              )
                            have h_7674 : Litex.Le _value_i13 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i13 h_7671).2.2
                                  )
                              )
                            have h_7675 : Litex.In _value_i13 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_1_0 _value_i13 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_7671)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i12;
                              let _litex_call_arg_1 := _value_i13;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                                exact h_5145) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i13;
                              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671) True.intro);
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
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i12;
                              let _litex_call_arg_1 := _value_i13;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                                exact h_5145) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i13;
                              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671) True.intro);
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
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24));
                        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), _raw_i13])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i13))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i13 : M.Value), M.mem _raw_i13 (Litex.denote _wd_1_0) → ((fun (_raw_i13 : M.Value) => True) _raw_i13) → M.mem ((fun (_raw_i13 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), _raw_i13])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i13))) _raw_i13) (Litex.denote (Litex.C (M := M))) := (by
                            intro _raw_i13 h_7671 _
                            let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_7671)
                            have h_7671 : Litex.In _value_i13 _wd_1_0 := h_7671
                            have h_7672 : Litex.In _value_i13 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i13 h_7671).1
                                  )
                              )
                            have h_7673 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i13 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i13 h_7671).2.1
                                  )
                              )
                            have h_7674 : Litex.Le _value_i13 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i13 h_7671).2.2
                                  )
                              )
                            have h_7675 : Litex.In _value_i13 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_1_0 _value_i13 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_7671)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i12;
                              let _litex_call_arg_1 := _value_i13;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                                exact h_5145) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i13;
                              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671) True.intro);
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
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i12;
                              let _litex_call_arg_1 := _value_i13;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                                exact h_5145) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i13;
                              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671) True.intro);
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
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .complex rfl)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.denote (Litex.C (M := M))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard)) (by rfl) (by rfl))).trans (let _equal_wd_2_0 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun (_captured_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i13 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i12, _raw_i13])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i13))) _captured_input)) _aggregate_item))))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) → ((fun (_raw_i12 : M.Value) => True) _raw_i12) → M.mem ((fun (_raw_i12 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun (_captured_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i13 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i12, _raw_i13])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i13))) _captured_input)) _aggregate_item))))) _raw_i12) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i12 h_5145 _
                      let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_5145)
                      have h_5145 : Litex.In _value_i12 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) := h_5145
                      have h_5146 : Litex.In _value_i12 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i12 h_5145).1
                            )
                        )
                      have h_5147 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i12 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i12 h_5145).2.1
                            )
                        )
                      have h_5148 : Litex.Le _value_i12 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i12 h_5145).2.2
                            )
                        )
                      have h_5149 : Litex.In _value_i12 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i12 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5145)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24));
                        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), _raw_i13])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i13))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i13 : M.Value), M.mem _raw_i13 (Litex.denote _wd_1_0) → ((fun (_raw_i13 : M.Value) => True) _raw_i13) → M.mem ((fun (_raw_i13 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), _raw_i13])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i13))) _raw_i13) (Litex.denote (Litex.C (M := M))) := (by
                            intro _raw_i13 h_7671 _
                            let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_7671)
                            have h_7671 : Litex.In _value_i13 _wd_1_0 := h_7671
                            have h_7672 : Litex.In _value_i13 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i13 h_7671).1
                                  )
                              )
                            have h_7673 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i13 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i13 h_7671).2.1
                                  )
                              )
                            have h_7674 : Litex.Le _value_i13 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i13 h_7671).2.2
                                  )
                              )
                            have h_7675 : Litex.In _value_i13 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_1_0 _value_i13 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_7671)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i12;
                              let _litex_call_arg_1 := _value_i13;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                                exact h_5145) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i13;
                              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671) True.intro);
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
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i12;
                              let _litex_call_arg_1 := _value_i13;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                                exact h_5145) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i13;
                              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671) True.intro);
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
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24));
                        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), _raw_i13])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i13))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i13 : M.Value), M.mem _raw_i13 (Litex.denote _wd_1_0) → ((fun (_raw_i13 : M.Value) => True) _raw_i13) → M.mem ((fun (_raw_i13 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), _raw_i13])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i13))) _raw_i13) (Litex.denote (Litex.C (M := M))) := (by
                            intro _raw_i13 h_7671 _
                            let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_7671)
                            have h_7671 : Litex.In _value_i13 _wd_1_0 := h_7671
                            have h_7672 : Litex.In _value_i13 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i13 h_7671).1
                                  )
                              )
                            have h_7673 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i13 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i13 h_7671).2.1
                                  )
                              )
                            have h_7674 : Litex.Le _value_i13 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i13 h_7671).2.2
                                  )
                              )
                            have h_7675 : Litex.In _value_i13 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_1_0 _value_i13 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_7671)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i12;
                              let _litex_call_arg_1 := _value_i13;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                                exact h_5145) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i13;
                              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671) True.intro);
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
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i12;
                              let _litex_call_arg_1 := _value_i13;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                                exact h_5145) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i13;
                              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_7671) True.intro);
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
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .complex rfl)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.denote (Litex.C (M := M))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  let _equal_wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i5, _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _captured_input)) _aggregate_item))))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => (M.number (Litex.finiteAggregateValue false (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i5, _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _captured_input)) _aggregate_item))))) _raw_i5) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i5 h_9722 _
                      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_9722)
                      have h_9722 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) := h_9722
                      have h_9723 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i5 h_9722).1
                            )
                        )
                      have h_9724 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i5 h_9722).2.1
                            )
                        )
                      have h_9725 : Litex.Le _value_i5 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i5 h_9722).2.2
                            )
                        )
                      have h_9726 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_9722)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24));
                        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
                            intro _raw_i6 h_12248 _
                            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_12248)
                            have h_12248 : Litex.In _value_i6 _wd_1_0 := h_12248
                            have h_12249 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_12248).1
                                  )
                              )
                            have h_12250 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_12248).2.1
                                  )
                              )
                            have h_12251 : Litex.Le _value_i6 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_12248).2.2
                                  )
                              )
                            have h_12252 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_12248)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                              let _litex_call_arg_1 := _value_i6;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                                exact h_9722) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_12248)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
                              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_12248) True.intro);
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
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                              let _litex_call_arg_1 := _value_i6;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                                exact h_9722) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_12248)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
                              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_12248) True.intro);
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
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24));
                        let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _litex_input) (by
                          have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
                            intro _raw_i6 h_12248 _
                            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_12248)
                            have h_12248 : Litex.In _value_i6 _wd_1_0 := h_12248
                            have h_12249 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_12248).1
                                  )
                              )
                            have h_12250 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_12248).2.1
                                  )
                              )
                            have h_12251 : Litex.Le _value_i6 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_12248).2.2
                                  )
                              )
                            have h_12252 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_12248)
                                  )
                              )
                            change (by
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                              let _litex_call_arg_1 := _value_i6;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                                exact h_9722) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_12248)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
                              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_12248) True.intro);
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
                              let _atomic_wd_2_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                              let _litex_call_arg_1 := _value_i6;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))), (Litex.denote _wd_1_0)] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22)))
                                have _finiteProof_1 := (Litex.isSet _wd_1_0)
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))
                                exact h_9722) (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_12248)) True.intro);
                              let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
                              Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_50 (by
                                let _atomic_wd_3_1 := _wd_1_0
                                exact h_12248) True.intro);
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
                          obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                          exact _litex_checked_return _litex_input _litex_members _litex_guard));
                        (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_24))
                          exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                        exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .complex rfl)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.denote (Litex.C (M := M))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_22))) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
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
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_vector_x5f_definition_x2f_statement_x2e_lit
