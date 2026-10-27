import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_multiplication_x5f_coordinates_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_29 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_31 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_33 : Litex.In _value_i3 (Litex.N (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_48 : Litex.In _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_29 h_31)) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_67 : Litex.In _value_i5 (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_31 h_33)) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_112 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_177 : Litex.In _value_i7 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))), (by
  let _object_h49 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_29 h_31)))
  have h_49 : Litex.In _value_i4 _object_h49 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_29 h_31) _object_h49 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_29 h_31))) h_48)
        )
    )
  let _object_h68 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_31 h_33)))
  have h_68 : Litex.In _value_i5 _object_h68 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i5 _value_i5 (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_31 h_33) _object_h68 (Litex.sameRefl _value_i5) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_31 h_33))) h_67)
        )
    )
  let _object_w23 := (let _litex_matrix_head := (Litex.matrixMultiply _value_i4 _value_i5 _value_i1 _value_i2 _value_i3 h_29 h_31 h_33 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_29 h_31)
    exact h_48) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_31 h_33)
    exact h_67));
  (let _litex_call_arg_0 := _value_i6;
  let _litex_call_arg_1 := _value_i7;
  Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixMultiplyInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
    exact h_112) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
    exact h_177)), True.intro⟩)))
  let _object_w24 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31));
  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _litex_input) (by
    have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote _wd_1_0) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _raw_i8) (Litex.denote (Litex.C (M := M))) := (by
      intro _raw_i8 h_4312 _
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4312)
      have h_4312 : Litex.In _value_i8 _wd_1_0 := h_4312
      have h_4313 : Litex.In _value_i8 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4312).1
            )
        )
      have h_4314 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i8 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4312).2.1
            )
        )
      have h_4315 : Litex.Le _value_i8 _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4312).2.2
            )
        )
      have h_4316 : Litex.In _value_i8 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive _wd_1_0 _value_i8 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4312)
            )
        )
      change (by
        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
        let _litex_call_arg_1 := _value_i8;
        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote _wd_1_0)] (by
          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
          have _finiteProof_1 := (Litex.isSet _wd_1_0)
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_49 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
          exact h_112) (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_4312)) True.intro);
        let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
        let _litex_call_arg_1 := _value_i7;
        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
          have _finiteProof_0 := (Litex.isSet _wd_1_0)
          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_68 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_4312) (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
          exact h_177)) True.intro);
        (Litex.mul _wd_2_0 _wd_2_1 (by
          let _atomic_wd_2_0 := _wd_2_0
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
          let _atomic_wd_2_0 := _wd_2_1
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
      exact (by
        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
        let _litex_call_arg_1 := _value_i8;
        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote _wd_1_0)] (by
          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
          have _finiteProof_1 := (Litex.isSet _wd_1_0)
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_49 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
          exact h_112) (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_4312)) True.intro);
        let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
        let _litex_call_arg_1 := _value_i7;
        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
          have _finiteProof_0 := (Litex.isSet _wd_1_0)
          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_68 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_4312) (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
          exact h_177)) True.intro);
        (Litex.mul _wd_2_0 _wd_2_1 (by
          let _atomic_wd_2_0 := _wd_2_0
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
          let _atomic_wd_2_0 := _wd_2_1
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
        exact (by
          let _arithmetic := _atomic_wd_1_0
          exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
    intro _litex_input _litex_domain
    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
    exact _litex_checked_return _litex_input _litex_members _litex_guard));
  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (by
    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
  exact (by
    let _equal_wd_1_0 := _object_w23
    let _equal_wd_1_1 := _object_w24
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_29 _Host_i2 _rep_i2 _value_i2 h_31 _Host_i3 _rep_i3 _value_i3 h_33 _Host_i4 _rep_i4 _value_i4 h_48 _Host_i5 _rep_i5 _value_i5 h_67 _Host_i6 _rep_i6 _value_i6 h_112 _Host_i7 _rep_i7 _value_i7 h_177
          have h_30 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_29)
                )
            )
          have h_32 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_31)
                )
            )
          have h_34 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i3 h_33)
                )
            )
          let _object_h49 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_29 h_31)))
          have h_49 : Litex.In _value_i4 _object_h49 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_29 h_31) _object_h49 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_29 h_31))) h_48)
                )
            )
          let _object_h68 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_31 h_33)))
          have h_68 : Litex.In _value_i5 _object_h68 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i5 _value_i5 (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_31 h_33) _object_h68 (Litex.sameRefl _value_i5) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_31 h_33))) h_67)
                )
            )
          have h_113 : Litex.In _value_i6 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i6 h_112).1
                )
            )
          have h_114 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i6 h_112).2.1
                )
            )
          have h_115 : Litex.Le _value_i6 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i6 h_112).2.2
                )
            )
          have h_116 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_112)
                )
            )
          have h_178 : Litex.In _value_i7 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i7 h_177).1
                )
            )
          have h_179 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i7 h_177).2.1
                )
            )
          have h_180 : Litex.Le _value_i7 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i7 h_177).2.2
                )
            )
          have h_181 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_177)
                )
            )
          let _object_w23 := (let _litex_matrix_head := (Litex.matrixMultiply _value_i4 _value_i5 _value_i1 _value_i2 _value_i3 h_29 h_31 h_33 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_29 h_31)
            exact h_48) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_31 h_33)
            exact h_67));
          (let _litex_call_arg_0 := _value_i6;
          let _litex_call_arg_1 := _value_i7;
          Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixMultiplyInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
            exact h_112) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
            exact h_177)), True.intro⟩)))
          let _object_w24 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31));
          let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote _wd_1_0) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _raw_i8) (Litex.denote (Litex.C (M := M))) := (by
              intro _raw_i8 h_4312 _
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4312)
              have h_4312 : Litex.In _value_i8 _wd_1_0 := h_4312
              have h_4313 : Litex.In _value_i8 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4312).1
                    )
                )
              have h_4314 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i8 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4312).2.1
                    )
                )
              have h_4315 : Litex.Le _value_i8 _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_4312).2.2
                    )
                )
              have h_4316 : Litex.In _value_i8 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_1_0 _value_i8 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4312)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                let _litex_call_arg_1 := _value_i8;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote _wd_1_0)] (by
                  have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
                  have _finiteProof_1 := (Litex.isSet _wd_1_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_49 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
                  exact h_112) (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_4312)) True.intro);
                let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
                let _litex_call_arg_1 := _value_i7;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_68 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_4312) (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
                  exact h_177)) True.intro);
                (Litex.mul _wd_2_0 _wd_2_1 (by
                  let _atomic_wd_2_0 := _wd_2_0
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                  let _atomic_wd_2_0 := _wd_2_1
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                let _litex_call_arg_1 := _value_i8;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote _wd_1_0)] (by
                  have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
                  have _finiteProof_1 := (Litex.isSet _wd_1_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_49 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
                  exact h_112) (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_4312)) True.intro);
                let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
                let _litex_call_arg_1 := _value_i7;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_68 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_4312) (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
                  exact h_177)) True.intro);
                (Litex.mul _wd_2_0 _wd_2_1 (by
                  let _atomic_wd_2_0 := _wd_2_0
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                  let _atomic_wd_2_0 := _wd_2_1
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact (by
                  let _arithmetic := _atomic_wd_1_0
                  exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
            exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
            exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w23
            let _equal_wd_1_1 := _object_w24
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w23;
                  let _equal_wd_1_1 := _object_w24;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show Litex.denote _equal_wd_1_0 = (M.number (Litex.finiteAggregateValue false (Litex.denote (_equal_wd_1_1).val.set) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (_equal_wd_1_1).val.set) (fun (_captured_input : M.Value) => (fun (_raw_i45 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i45 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i45])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i45, (Litex.denote _value_i7)])))) _captured_input)) _aggregate_item)))) from by
                    have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i6 _value_i7))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.matrixMultiplyCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i6 _value_i7)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) (fun (_litex_input : M.Value) => (fun (_raw_i43 : M.Value) (_raw_i44 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i6 _value_i7))).mpr ⟨(Litex.callArguments2_mem_cart _value_i6 _value_i7 (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
                    exact h_112) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
                    exact h_177)), True.intro⟩))
                    change Litex.denote _equal_wd_1_0 = Litex.matrixMultiplyBody (Litex.denote ((_equal_wd_1_0).val.function).val.left) (Litex.denote ((_equal_wd_1_0).val.function).val.right) ((_equal_wd_1_0).val.function).val.inner (Litex.FiniteFunction.pack2 (Litex.denote _value_i6) (Litex.denote _value_i7)) at h
                    unfold Litex.matrixMultiplyBody Litex.matrixMultiplyTerm at h
                    rw [Litex.FiniteFunction.unpack_pack2] at h
                    exact h).trans (show (M.number (Litex.finiteAggregateValue false (Litex.denote (_equal_wd_1_1).val.set) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (_equal_wd_1_1).val.set) (fun (_captured_input : M.Value) => (fun (_raw_i45 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i45 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i45])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i45, (Litex.denote _value_i7)])))) _captured_input)) _aggregate_item)))) = (Litex.denote (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i45])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i45, (Litex.denote _value_i7)])))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i45 : M.Value), M.mem _raw_i45 (Litex.denote _wd_1_0) → ((fun (_raw_i45 : M.Value) => True) _raw_i45) → M.mem ((fun (_raw_i45 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i45])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i45, (Litex.denote _value_i7)])))) _raw_i45) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i45 h_8157 _
                      let _value_i45 := Litex.semanticObject (M := M) _raw_i45 (M.member_isSet h_8157)
                      have h_8157 : Litex.In _value_i45 _wd_1_0 := h_8157
                      have h_8158 : Litex.In _value_i45 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i45 h_8157).1
                            )
                        )
                      have h_8159 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i45 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i45 h_8157).2.1
                            )
                        )
                      have h_8160 : Litex.Le _value_i45 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i45 h_8157).2.2
                            )
                        )
                      have h_8161 : Litex.In _value_i45 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i45 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_8157)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i45;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_49 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
                          exact h_112) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_8157)) True.intro);
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i45;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_68 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_8157) (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
                          exact h_177)) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := _wd_2_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i45;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_49 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
                          exact h_112) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_8157)) True.intro);
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i45;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_68 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_8157) (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
                          exact h_177)) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := _wd_2_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact (by
                          let _arithmetic := _atomic_wd_1_0
                          exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))) from rfl)).trans (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i45])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i45, (Litex.denote _value_i7)])))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i45 : M.Value), M.mem _raw_i45 (Litex.denote _wd_1_0) → ((fun (_raw_i45 : M.Value) => True) _raw_i45) → M.mem ((fun (_raw_i45 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i45])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i45, (Litex.denote _value_i7)])))) _raw_i45) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i45 h_8157 _
                      let _value_i45 := Litex.semanticObject (M := M) _raw_i45 (M.member_isSet h_8157)
                      have h_8157 : Litex.In _value_i45 _wd_1_0 := h_8157
                      have h_8158 : Litex.In _value_i45 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i45 h_8157).1
                            )
                        )
                      have h_8159 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i45 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i45 h_8157).2.1
                            )
                        )
                      have h_8160 : Litex.Le _value_i45 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i45 h_8157).2.2
                            )
                        )
                      have h_8161 : Litex.In _value_i45 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i45 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_8157)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i45;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_49 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
                          exact h_112) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_8157)) True.intro);
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i45;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_68 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_8157) (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
                          exact h_177)) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := _wd_2_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i45;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_49 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
                          exact h_112) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_8157)) True.intro);
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i45;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_68 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_8157) (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
                          exact h_177)) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := _wd_2_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact (by
                          let _arithmetic := _atomic_wd_1_0
                          exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
                  let _equal_wd_2_1 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote _wd_1_0) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i6), _raw_i8])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, (Litex.denote _value_i7)])))) _raw_i8) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i8 h_10983 _
                      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_10983)
                      have h_10983 : Litex.In _value_i8 _wd_1_0 := h_10983
                      have h_10984 : Litex.In _value_i8 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_10983).1
                            )
                        )
                      have h_10985 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i8 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_10983).2.1
                            )
                        )
                      have h_10986 : Litex.Le _value_i8 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_10983).2.2
                            )
                        )
                      have h_10987 : Litex.In _value_i8 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i8 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_10983)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i8;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_49 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
                          exact h_112) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_10983)) True.intro);
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_68 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_10983) (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
                          exact h_177)) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := _wd_2_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i6;
                        let _litex_call_arg_1 := _value_i8;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_49 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
                          exact h_112) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_10983)) True.intro);
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i8;
                        let _litex_call_arg_1 := _value_i7;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i5 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_68 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_10983) (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
                          exact h_177)) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := _wd_2_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact (by
                          let _arithmetic := _atomic_wd_1_0
                          exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (by
                    let _left := _equal_wd_2_0
                    let _right := _equal_wd_2_1
                    exact (show Litex.Same _left _right from rfl)))))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_multiplication_x5f_coordinates_x2f_statement_x2e_lit
