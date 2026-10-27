import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_trace_x5f_definition_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_32 : Litex.In _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)), (by
  let _object_h33 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)))
  have h_33 : Litex.In _value_i2 _object_h33 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i2 _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19) _object_h33 (Litex.sameRefl _value_i2) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19))) h_32)
        )
    )
  let _object_w17 := (Litex.matrixTrace _value_i2 _value_i1 h_19 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)
    exact h_32))
  let _object_w18 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i3, _raw_i3]))) _litex_input) (by
    have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i3, _raw_i3]))) _raw_i3) (Litex.denote (Litex.C (M := M))) := (by
      intro _raw_i3 h_244 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_244)
      have h_244 : Litex.In _value_i3 _wd_1_0 := h_244
      have h_245 : Litex.In _value_i3 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_244).1
            )
        )
      have h_246 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_244).2.1
            )
        )
      have h_247 : Litex.Le _value_i3 _value_i1 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_244).2.2
            )
        )
      have h_248 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_244)
            )
        )
      change (by
        let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i3;
        let _litex_call_arg_1 := _value_i3;
        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_1_0)] (by
          have _finiteProof_0 := (Litex.isSet _wd_1_0)
          have _finiteProof_1 := (Litex.isSet _wd_1_0)
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i2 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_33 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_244) (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_244)) True.intro)
        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
      exact (by
        let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i3;
        let _litex_call_arg_1 := _value_i3;
        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_1_0)] (by
          have _finiteProof_0 := (Litex.isSet _wd_1_0)
          have _finiteProof_1 := (Litex.isSet _wd_1_0)
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i2 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_33 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_244) (by
          let _atomic_wd_2_1 := _wd_1_0
          exact h_244)) True.intro)
        exact (by
          let _litex_return_call := _atomic_wd_1_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))))
    intro _litex_input _litex_domain
    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
    exact _litex_checked_return _litex_input _litex_members _litex_guard));
  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
  exact (by
    let _equal_wd_1_0 := _object_w17
    let _equal_wd_1_1 := _object_w18
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_19 _Host_i2 _rep_i2 _value_i2 h_32
          have h_20 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_19)
                )
            )
          let _object_h33 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)))
          have h_33 : Litex.In _value_i2 _object_h33 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19) _object_h33 (Litex.sameRefl _value_i2) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19))) h_32)
                )
            )
          let _object_w17 := (Litex.matrixTrace _value_i2 _value_i1 h_19 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)
            exact h_32))
          let _object_w18 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
          let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i3, _raw_i3]))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i3, _raw_i3]))) _raw_i3) (Litex.denote (Litex.C (M := M))) := (by
              intro _raw_i3 h_244 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_244)
              have h_244 : Litex.In _value_i3 _wd_1_0 := h_244
              have h_245 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_244).1
                    )
                )
              have h_246 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_244).2.1
                    )
                )
              have h_247 : Litex.Le _value_i3 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_244).2.2
                    )
                )
              have h_248 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_244)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i3;
                let _litex_call_arg_1 := _value_i3;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_1_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_1_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i2 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_33 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_244) (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_244)) True.intro)
                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i3;
                let _litex_call_arg_1 := _value_i3;
                Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_1_0)] (by
                  have _finiteProof_0 := (Litex.isSet _wd_1_0)
                  have _finiteProof_1 := (Litex.isSet _wd_1_0)
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i2 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_33 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_244) (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_244)) True.intro)
                exact (by
                  let _litex_return_call := _atomic_wd_1_0
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
            exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
            exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w17;
                  let _equal_wd_1_1 := _object_w18;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((show Litex.Same _equal_wd_1_0 (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, _raw_i8]))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote _wd_1_0) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, _raw_i8]))) _raw_i8) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i8 h_722 _
                      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_722)
                      have h_722 : Litex.In _value_i8 _wd_1_0 := h_722
                      have h_723 : Litex.In _value_i8 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_722).1
                            )
                        )
                      have h_724 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i8 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_722).2.1
                            )
                        )
                      have h_725 : Litex.Le _value_i8 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_722).2.2
                            )
                        )
                      have h_726 : Litex.In _value_i8 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i8 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_722)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i8;
                        let _litex_call_arg_1 := _value_i8;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i2 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_33 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_722) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_722)) True.intro)
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i8;
                        let _litex_call_arg_1 := _value_i8;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i2 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_33 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_722) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_722)) True.intro)
                        exact (by
                          let _litex_return_call := _atomic_wd_1_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) from Litex.matrixTraceFormula _equal_wd_1_0 ((let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, _raw_i8]))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote _wd_1_0) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, _raw_i8]))) _raw_i8) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i8 h_722 _
                      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_722)
                      have h_722 : Litex.In _value_i8 _wd_1_0 := h_722
                      have h_723 : Litex.In _value_i8 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_722).1
                            )
                        )
                      have h_724 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i8 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_722).2.1
                            )
                        )
                      have h_725 : Litex.Le _value_i8 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_722).2.2
                            )
                        )
                      have h_726 : Litex.In _value_i8 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i8 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_722)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i8;
                        let _litex_call_arg_1 := _value_i8;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i2 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_33 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_722) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_722)) True.intro)
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i8;
                        let _litex_call_arg_1 := _value_i8;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i2 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_33 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_722) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_722)) True.intro)
                        exact (by
                          let _litex_return_call := _atomic_wd_1_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))).val.function (by rfl) (by rfl)).trans (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, _raw_i8]))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote _wd_1_0) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i8, _raw_i8]))) _raw_i8) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i8 h_722 _
                      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_722)
                      have h_722 : Litex.In _value_i8 _wd_1_0 := h_722
                      have h_723 : Litex.In _value_i8 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_722).1
                            )
                        )
                      have h_724 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i8 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_722).2.1
                            )
                        )
                      have h_725 : Litex.Le _value_i8 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i8 h_722).2.2
                            )
                        )
                      have h_726 : Litex.In _value_i8 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i8 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_722)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i8;
                        let _litex_call_arg_1 := _value_i8;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i2 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_33 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_722) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_722)) True.intro)
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i8;
                        let _litex_call_arg_1 := _value_i8;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i2 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_33 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_722) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_722)) True.intro)
                        exact (by
                          let _litex_return_call := _atomic_wd_1_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetRefl (Litex.C (M := M))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
                  let _equal_wd_2_1 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i3, _raw_i3]))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i3, _raw_i3]))) _raw_i3) (Litex.denote (Litex.C (M := M))) := (by
                      intro _raw_i3 h_1154 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1154)
                      have h_1154 : Litex.In _value_i3 _wd_1_0 := h_1154
                      have h_1155 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1154).1
                            )
                        )
                      have h_1156 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1154).2.1
                            )
                        )
                      have h_1157 : Litex.Le _value_i3 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1154).2.2
                            )
                        )
                      have h_1158 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1154)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i3;
                        let _litex_call_arg_1 := _value_i3;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i2 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_33 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_1154) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_1154)) True.intro)
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i3;
                        let _litex_call_arg_1 := _value_i3;
                        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _wd_1_0), (Litex.denote _wd_1_0)] (by
                          have _finiteProof_0 := (Litex.isSet _wd_1_0)
                          have _finiteProof_1 := (Litex.isSet _wd_1_0)
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i2 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_33 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_1154) (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_1154)) True.intro)
                        exact (by
                          let _litex_return_call := _atomic_wd_1_0
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.C (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
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
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_trace_x5f_definition_x2f_statement_x2e_lit
