import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_vector_x5f_coordinates_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_25 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_27 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_42 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_52 : Litex.In _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_27)) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_92 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (by
  let _object_h43 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)))
  have h_43 : Litex.In _value_i3 _object_h43 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27) _object_h43 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27))) h_42)
        )
    )
  let _object_h53 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_27)))
  have h_53 : Litex.In _value_i4 _object_h53 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i4 _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_27) _object_h53 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_27)) h_52)
        )
    )
  let _object_w22 := (let _litex_matrix_head := (Litex.matrixApply _value_i3 _value_i4 _value_i1 _value_i2 h_25 h_27 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
    exact h_42) (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_27)
    exact h_52));
  (let _litex_call_arg_0 := _value_i5;
  Litex.callOn (Litex.matrixApplySignature (_litex_matrix_head).val.rows .complex) _litex_matrix_head _litex_call_arg_0 (Litex.matrixApplyInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
    exact h_92), True.intro⟩)))
  let _object_w23 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27));
  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _litex_input) (by
    have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
      intro _raw_i6 h_3334 _
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_3334)
      have h_3334 : Litex.In _value_i6 _wd_1_0 := h_3334
      have h_3335 : Litex.In _value_i6 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_3334).1
            )
        )
      have h_3336 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_3334).2.1
            )
        )
      have h_3337 : Litex.Le _value_i6 _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_3334).2.2
            )
        )
      have h_3338 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3334)
            )
        )
      change (by
        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
        let _litex_call_arg_1 := _value_i6;
        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote _wd_1_0)] (by
          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
          have _finiteProof_1 := (Litex.isSet _wd_1_0)
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
          exact h_92) (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_3334)) True.intro);
        let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_53 (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_3334) True.intro);
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
        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
        let _litex_call_arg_1 := _value_i6;
        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote _wd_1_0)] (by
          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
          have _finiteProof_1 := (Litex.isSet _wd_1_0)
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
          exact h_92) (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_3334)) True.intro);
        let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_53 (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_3334) True.intro);
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
    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
    exact _litex_checked_return _litex_input _litex_members _litex_guard));
  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
  exact (by
    let _equal_wd_1_0 := _object_w22
    let _equal_wd_1_1 := _object_w23
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_25 _Host_i2 _rep_i2 _value_i2 h_27 _Host_i3 _rep_i3 _value_i3 h_42 _Host_i4 _rep_i4 _value_i4 h_52 _Host_i5 _rep_i5 _value_i5 h_92
          have h_26 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_25)
                )
            )
          have h_28 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_27)
                )
            )
          let _object_h43 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)))
          have h_43 : Litex.In _value_i3 _object_h43 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27) _object_h43 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27))) h_42)
                )
            )
          let _object_h53 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_27)))
          have h_53 : Litex.In _value_i4 _object_h53 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_27) _object_h53 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_27)) h_52)
                )
            )
          have h_93 : Litex.In _value_i5 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i5 h_92).1
                )
            )
          have h_94 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i5 h_92).2.1
                )
            )
          have h_95 : Litex.Le _value_i5 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i5 h_92).2.2
                )
            )
          have h_96 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_92)
                )
            )
          let _object_w22 := (let _litex_matrix_head := (Litex.matrixApply _value_i3 _value_i4 _value_i1 _value_i2 h_25 h_27 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
            exact h_42) (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_27)
            exact h_52));
          (let _litex_call_arg_0 := _value_i5;
          Litex.callOn (Litex.matrixApplySignature (_litex_matrix_head).val.rows .complex) _litex_matrix_head _litex_call_arg_0 (Litex.matrixApplyInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
            exact h_92), True.intro⟩)))
          let _object_w23 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27));
          let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
              intro _raw_i6 h_3334 _
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_3334)
              have h_3334 : Litex.In _value_i6 _wd_1_0 := h_3334
              have h_3335 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_3334).1
                    )
                )
              have h_3336 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_3334).2.1
                    )
                )
              have h_3337 : Litex.Le _value_i6 _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_3334).2.2
                    )
                )
              have h_3338 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3334)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                let _litex_call_arg_1 := _value_i6;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote _wd_1_0)] (by
                  have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                  have _finiteProof_1 := (Litex.isSet _wd_1_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
                  exact h_92) (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_3334)) True.intro);
                let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
                Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_53 (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_3334) True.intro);
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
                let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                let _litex_call_arg_1 := _value_i6;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote _wd_1_0)] (by
                  have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                  have _finiteProof_1 := (Litex.isSet _wd_1_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
                  exact h_92) (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_3334)) True.intro);
                let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
                Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_53 (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_3334) True.intro);
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
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
            exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
            exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w22
            let _equal_wd_1_1 := _object_w23
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w22;
                  let _equal_wd_1_1 := _object_w23;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show Litex.denote _equal_wd_1_0 = (M.number (Litex.finiteAggregateValue false (Litex.denote (_equal_wd_1_1).val.set) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (_equal_wd_1_1).val.set) (fun (_captured_input : M.Value) => (fun (_raw_i36 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i36 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i36])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i36))) _captured_input)) _aggregate_item)))) from (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _value_i5)) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.matrixApplyCall (_equal_wd_1_0).val.function (Litex.denote _value_i5) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))) (fun (_litex_input : M.Value) => (fun (_raw_i35 : M.Value) => True) _litex_input) (Litex.denote _value_i5)).mpr ⟨(by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
                    exact h_92), True.intro⟩))).trans (show (M.number (Litex.finiteAggregateValue false (Litex.denote (_equal_wd_1_1).val.set) (fun _aggregate_item => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.denote (_equal_wd_1_1).val.set) (fun (_captured_input : M.Value) => (fun (_raw_i36 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.complex) (fun (_captured_input : M.Value) => (fun (_raw_i36 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i36])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i36))) _captured_input)) _aggregate_item)))) = (Litex.denote (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i36 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i36 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i36])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i36))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i36 : M.Value), M.mem _raw_i36 (Litex.denote _wd_1_0) → ((fun (_raw_i36 : M.Value) => True) _raw_i36) → M.mem ((fun (_raw_i36 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i36])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i36))) _raw_i36) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i36 h_6113 _
                      let _value_i36 := Litex.semanticObject (M := M) _raw_i36 (M.member_isSet h_6113)
                      have h_6113 : Litex.In _value_i36 _wd_1_0 := h_6113
                      have h_6114 : Litex.In _value_i36 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i36 h_6113).1
                            )
                        )
                      have h_6115 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i36 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i36 h_6113).2.1
                            )
                        )
                      have h_6116 : Litex.Le _value_i36 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i36 h_6113).2.2
                            )
                        )
                      have h_6117 : Litex.In _value_i36 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i36 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6113)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                        let _litex_call_arg_1 := _value_i36;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
                          exact h_92) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_6113)) True.intro);
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i36;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_53 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_6113) True.intro);
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
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                        let _litex_call_arg_1 := _value_i36;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
                          exact h_92) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_6113)) True.intro);
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i36;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_53 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_6113) True.intro);
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
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i36 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i36 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))) from rfl)).trans (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i36 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i36 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i36])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i36))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i36 : M.Value), M.mem _raw_i36 (Litex.denote _wd_1_0) → ((fun (_raw_i36 : M.Value) => True) _raw_i36) → M.mem ((fun (_raw_i36 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i36])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i36))) _raw_i36) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i36 h_6113 _
                      let _value_i36 := Litex.semanticObject (M := M) _raw_i36 (M.member_isSet h_6113)
                      have h_6113 : Litex.In _value_i36 _wd_1_0 := h_6113
                      have h_6114 : Litex.In _value_i36 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i36 h_6113).1
                            )
                        )
                      have h_6115 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i36 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i36 h_6113).2.1
                            )
                        )
                      have h_6116 : Litex.Le _value_i36 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i36 h_6113).2.2
                            )
                        )
                      have h_6117 : Litex.In _value_i36 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i36 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6113)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                        let _litex_call_arg_1 := _value_i36;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
                          exact h_92) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_6113)) True.intro);
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i36;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_53 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_6113) True.intro);
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
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                        let _litex_call_arg_1 := _value_i36;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
                          exact h_92) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_6113)) True.intro);
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i36;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_53 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_6113) True.intro);
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
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i36 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i36 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
                  let _equal_wd_2_1 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), _raw_i6])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) _raw_i6))) _raw_i6) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i6 h_8176 _
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_8176)
                      have h_8176 : Litex.In _value_i6 _wd_1_0 := h_8176
                      have h_8177 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_8176).1
                            )
                        )
                      have h_8178 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_8176).2.1
                            )
                        )
                      have h_8179 : Litex.Le _value_i6 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_8176).2.2
                            )
                        )
                      have h_8180 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_8176)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                        let _litex_call_arg_1 := _value_i6;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
                          exact h_92) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_8176)) True.intro);
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_53 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_8176) True.intro);
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
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := _value_i5;
                        let _litex_call_arg_1 := _value_i6;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
                          exact h_92) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_8176)) True.intro);
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i6;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_53 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_8176) True.intro);
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
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
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
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_vector_x5f_coordinates_x2f_statement_x2e_lit
