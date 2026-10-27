import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_inner_x5f_product_x5f_definition_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_18 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_26 : Litex.In _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_28 : Litex.In _value_i3 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)), (by
  let _object_h27 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)))
  have h_27 : Litex.In _value_i2 _object_h27 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18) _object_h27 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)) h_26)
        )
    )
  let _object_h29 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)))
  have h_29 : Litex.In _value_i3 _object_h29 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i3 _value_i3 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18) _object_h29 (Litex.sameRefl _value_i3) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)) h_28)
        )
    )
  let _object_w18 := (Litex.finiteInnerProduct _value_i2 _value_i3 _value_i1 h_18 (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
    exact h_26) (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
    exact h_28))
  let _object_w19 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18));
  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.mulValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i4))) _litex_input) (by
    have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.mulValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i4))) _raw_i4) (Litex.denote (Litex.C (M := M))) := (by
      intro _raw_i4 h_331 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_331)
      have h_331 : Litex.In _value_i4 _wd_1_0 := h_331
      have h_332 : Litex.In _value_i4 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_331).1
            )
        )
      have h_333 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_331).2.1
            )
        )
      have h_334 : Litex.Le _value_i4 _value_i1 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_331).2.2
            )
        )
      have h_335 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_331)
            )
        )
      change (by
        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i4;
        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_331) True.intro);
        (Litex.conj _wd_3_0 (by
          let _atomic_wd_2_0 := _wd_3_0
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
        let _wd_2_1 := (let _litex_call_arg_0 := _value_i4;
        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_29 (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_331) True.intro);
        (Litex.mul _wd_2_0 _wd_2_1 (by
          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
          (Litex.conj _wd_3_0 (by
            let _atomic_wd_3_0 := _wd_3_0
            exact (by
              let _litex_return_call := _atomic_wd_3_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
          exact (Litex.conjInC _atomic_wd_2_0)) (by
          let _atomic_wd_2_0 := _wd_2_1
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
      exact (by
        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i4;
        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_331) True.intro);
        (Litex.conj _wd_3_0 (by
          let _atomic_wd_2_0 := _wd_3_0
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
        let _wd_2_1 := (let _litex_call_arg_0 := _value_i4;
        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_29 (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_331) True.intro);
        (Litex.mul _wd_2_0 _wd_2_1 (by
          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
          (Litex.conj _wd_3_0 (by
            let _atomic_wd_3_0 := _wd_3_0
            exact (by
              let _litex_return_call := _atomic_wd_3_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
          exact (Litex.conjInC _atomic_wd_2_0)) (by
          let _atomic_wd_2_0 := _wd_2_1
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
        exact (by
          let _arithmetic := _atomic_wd_1_0
          exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
    intro _litex_input _litex_domain
    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
    exact _litex_checked_return _litex_input _litex_members _litex_guard));
  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
  exact (by
    let _equal_wd_1_0 := _object_w18
    let _equal_wd_1_1 := _object_w19
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_18 _Host_i2 _rep_i2 _value_i2 h_26 _Host_i3 _rep_i3 _value_i3 h_28
          have h_19 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_18)
                )
            )
          let _object_h27 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)))
          have h_27 : Litex.In _value_i2 _object_h27 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18) _object_h27 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)) h_26)
                )
            )
          let _object_h29 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)))
          have h_29 : Litex.In _value_i3 _object_h29 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18) _object_h29 (Litex.sameRefl _value_i3) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)) h_28)
                )
            )
          let _object_w18 := (Litex.finiteInnerProduct _value_i2 _value_i3 _value_i1 h_18 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
            exact h_26) (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
            exact h_28))
          let _object_w19 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18));
          let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.mulValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i4))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.mulValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i4))) _raw_i4) (Litex.denote (Litex.C (M := M))) := (by
              intro _raw_i4 h_331 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_331)
              have h_331 : Litex.In _value_i4 _wd_1_0 := h_331
              have h_332 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_331).1
                    )
                )
              have h_333 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_331).2.1
                    )
                )
              have h_334 : Litex.Le _value_i4 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_331).2.2
                    )
                )
              have h_335 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_331)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i4;
                Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_331) True.intro);
                (Litex.conj _wd_3_0 (by
                  let _atomic_wd_2_0 := _wd_3_0
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_2_1 := (let _litex_call_arg_0 := _value_i4;
                Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_29 (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_331) True.intro);
                (Litex.mul _wd_2_0 _wd_2_1 (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                  (Litex.conj _wd_3_0 (by
                    let _atomic_wd_3_0 := _wd_3_0
                    exact (by
                      let _litex_return_call := _atomic_wd_3_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.conjInC _atomic_wd_2_0)) (by
                  let _atomic_wd_2_0 := _wd_2_1
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i4;
                Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_331) True.intro);
                (Litex.conj _wd_3_0 (by
                  let _atomic_wd_2_0 := _wd_3_0
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_2_1 := (let _litex_call_arg_0 := _value_i4;
                Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_29 (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_331) True.intro);
                (Litex.mul _wd_2_0 _wd_2_1 (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                  (Litex.conj _wd_3_0 (by
                    let _atomic_wd_3_0 := _wd_3_0
                    exact (by
                      let _litex_return_call := _atomic_wd_3_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.conjInC _atomic_wd_2_0)) (by
                  let _atomic_wd_2_0 := _wd_2_1
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                exact (by
                  let _arithmetic := _atomic_wd_1_0
                  exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
            exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
            exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w18
            let _equal_wd_1_1 := _object_w19
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w18;
                  let _equal_wd_1_1 := _object_w19;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((show Litex.Same _equal_wd_1_0 (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (M.mulValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i9))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (Litex.denote _wd_1_0) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → M.mem ((fun (_raw_i9 : M.Value) => (M.mulValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i9))) _raw_i9) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i9 h_2200 _
                      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_2200)
                      have h_2200 : Litex.In _value_i9 _wd_1_0 := h_2200
                      have h_2201 : Litex.In _value_i9 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_2200).1
                            )
                        )
                      have h_2202 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i9 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_2200).2.1
                            )
                        )
                      have h_2203 : Litex.Le _value_i9 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_2200).2.2
                            )
                        )
                      have h_2204 : Litex.In _value_i9 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i9 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2200)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i9;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_2200) True.intro);
                        (Litex.conj _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i9;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_29 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_2200) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.conj _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.conjInC _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i9;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_2200) True.intro);
                        (Litex.conj _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i9;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_29 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_2200) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.conj _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.conjInC _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact (by
                          let _arithmetic := _atomic_wd_1_0
                          exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) from Litex.finiteInnerProductFormula _equal_wd_1_0 ((let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (M.mulValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i9))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (Litex.denote _wd_1_0) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → M.mem ((fun (_raw_i9 : M.Value) => (M.mulValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i9))) _raw_i9) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i9 h_2200 _
                      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_2200)
                      have h_2200 : Litex.In _value_i9 _wd_1_0 := h_2200
                      have h_2201 : Litex.In _value_i9 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_2200).1
                            )
                        )
                      have h_2202 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i9 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_2200).2.1
                            )
                        )
                      have h_2203 : Litex.Le _value_i9 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_2200).2.2
                            )
                        )
                      have h_2204 : Litex.In _value_i9 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i9 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2200)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i9;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_2200) True.intro);
                        (Litex.conj _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i9;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_29 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_2200) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.conj _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.conjInC _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i9;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_2200) True.intro);
                        (Litex.conj _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i9;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_29 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_2200) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.conj _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.conjInC _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact (by
                          let _arithmetic := _atomic_wd_1_0
                          exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))).val.function (by rfl) (by rfl)).trans (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (M.mulValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i9))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (Litex.denote _wd_1_0) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → M.mem ((fun (_raw_i9 : M.Value) => (M.mulValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i9))) _raw_i9) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i9 h_2200 _
                      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_2200)
                      have h_2200 : Litex.In _value_i9 _wd_1_0 := h_2200
                      have h_2201 : Litex.In _value_i9 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_2200).1
                            )
                        )
                      have h_2202 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i9 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_2200).2.1
                            )
                        )
                      have h_2203 : Litex.Le _value_i9 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i9 h_2200).2.2
                            )
                        )
                      have h_2204 : Litex.In _value_i9 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i9 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2200)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i9;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_2200) True.intro);
                        (Litex.conj _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i9;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_29 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_2200) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.conj _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.conjInC _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i9;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_2200) True.intro);
                        (Litex.conj _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i9;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_29 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_2200) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.conj _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.conjInC _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact (by
                          let _arithmetic := _atomic_wd_1_0
                          exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
                  let _equal_wd_2_1 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.mulValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i4))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_1_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.mulValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) _raw_i4))) _raw_i4) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i4 h_3990 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_3990)
                      have h_3990 : Litex.In _value_i4 _wd_1_0 := h_3990
                      have h_3991 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_3990).1
                            )
                        )
                      have h_3992 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_3990).2.1
                            )
                        )
                      have h_3993 : Litex.Le _value_i4 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i4 h_3990).2.2
                            )
                        )
                      have h_3994 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3990)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i4;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_3990) True.intro);
                        (Litex.conj _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i4;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_29 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_3990) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.conj _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.conjInC _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i4;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_3990) True.intro);
                        (Litex.conj _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (let _litex_call_arg_0 := _value_i4;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_29 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_3990) True.intro);
                        (Litex.mul _wd_2_0 _wd_2_1 (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.conj _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.conjInC _atomic_wd_2_0)) (by
                          let _atomic_wd_2_0 := _wd_2_1
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                        exact (by
                          let _arithmetic := _atomic_wd_1_0
                          exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
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
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_inner_x5f_product_x5f_definition_x2f_statement_x2e_lit
