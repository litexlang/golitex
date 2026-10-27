import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_fold_x5f_last_x5f_step_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v6 v9
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_20 : Litex.In _value_i1 (Litex.Z (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_21 : Litex.In _value_i2 (Litex.Z (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_22 : Litex.IsSet _value_i3) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_24 : Litex.In _value_i4 (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.Z (M := M))) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → True := (by
    intro _raw_i5 h_23 _
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_23)
    have h_23 : Litex.In _value_i5 (Litex.Z (M := M)) := h_23
    exact True.intro);
  Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_27 : Litex.In _value_i6 (let _checked_header : ∀ (_raw_i7 : M.Value) (_raw_i8 : M.Value), M.mem _raw_i7 (Litex.denote _value_i3) → M.mem _raw_i8 (Litex.denote _value_i3) → ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _raw_i7 _raw_i8) → True := (by
    intro _raw_i7 _raw_i8 h_25 h_26 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_25)
    have h_25 : Litex.In _value_i7 _value_i3 := h_25
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_26)
    have h_26 : Litex.In _value_i8 _value_i3 := h_26
    exact True.intro);
  Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
  have _finiteProof_0 := (Litex.isSet _value_i3)
  have _finiteProof_1 := (Litex.isSet _value_i3)
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_28 : Litex.In _value_i9 _value_i3) (h_1 : Litex.Le _value_i1 _value_i2), (by
  let _object_w11 := (let h_173 : Litex.In _value_i1 (Litex.Z (M := M)) := h_20;
  let h_178 : Litex.In _value_i2 (Litex.Z (M := M)) := h_21;
  let h_185 : Litex.In _value_i9 _value_i3 := h_28;
  Litex.rangeFold _value_i1 _value_i2 _value_i4 _value_i6 _value_i9 (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) h_173 h_178 (Litex.inOfSame _value_i4 _value_i4 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input))) (Litex.sameRefl _value_i4) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)))) h_24) (Litex.inOfSame _value_i6 _value_i6 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
    have _finiteProof_0 := (Litex.isSet _value_i3)
    have _finiteProof_1 := (Litex.isSet _value_i3)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
    have _finiteProof_0 := (Litex.isSet _value_i3)
    have _finiteProof_1 := (Litex.isSet _value_i3)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.sameRefl _value_i6) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
    have _finiteProof_0 := (Litex.isSet _value_i3)
    have _finiteProof_1 := (Litex.isSet _value_i3)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))) h_27) h_185 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.Z (M := M))) (Litex.denote _value_i3) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _value_i3) (fun (_raw_i5 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩))
  let _object_w12 := (let _object_w5 := (let _wd_2_0 := _value_i1;
  let _wd_2_1 := (Litex.sub _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i2 h_21) (Litex.numberInC (M := M) (1 : ℂ)));
  let _wd_2_2 := _value_i4;
  let _wd_2_3 := _value_i6;
  let _wd_2_4 := _value_i9;
  (let h_237 : Litex.In _wd_2_0 (Litex.Z (M := M)) := h_20;
  let h_242 : (by
    let _atomic_wd_1_0 := _wd_2_1
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) := (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (Litex.subInZ _value_i2 (Litex.number (M := M) (1 : ℂ)) h_21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))));
  let h_313 : Litex.In _wd_2_4 _value_i3 := h_28;
  Litex.rangeFold _wd_2_0 _wd_2_1 _wd_2_2 _wd_2_3 _wd_2_4 (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) h_237 h_242 (Litex.inOfSame _wd_2_2 _wd_2_2 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input))) (Litex.sameRefl _wd_2_2) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)))) h_24) (Litex.inOfSame _wd_2_3 _wd_2_3 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
    have _finiteProof_0 := (Litex.isSet _value_i3)
    have _finiteProof_1 := (Litex.isSet _value_i3)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
    have _finiteProof_0 := (Litex.isSet _value_i3)
    have _finiteProof_1 := (Litex.isSet _value_i3)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.sameRefl _wd_2_3) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
    have _finiteProof_0 := (Litex.isSet _value_i3)
    have _finiteProof_1 := (Litex.isSet _value_i3)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))) h_27) h_313 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.Z (M := M))) (Litex.denote _value_i3) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _value_i3) (fun (_raw_i5 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)));
  let _object_w6 := (let _litex_call_arg_0 := _value_i2;
  Litex.callOnDomain (Litex.Z (M := M)) _value_i3 (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_24 h_21 True.intro);
  (let _litex_call_arg_0 := _object_w5;
  let _litex_call_arg_1 := _object_w6;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
    have _finiteProof_0 := (Litex.isSet _value_i3)
    have _finiteProof_1 := (Litex.isSet _value_i3)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) _value_i3 (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i6 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_27 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_0 := _object_w5
    exact (by
      have _selected_operation : Litex.In _value_i6 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
      have _finiteProof_0 := (Litex.isSet _value_i3)
      have _finiteProof_1 := (Litex.isSet _value_i3)
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) := h_27
      exact Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 _value_i3 _value_i3 (Litex.sameRefl _atomic_wd_1_0) (Litex.sameRefl _value_i3) (Litex.rangeFoldInOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _object_w6
    exact (by
      let _litex_return_call := _object_w6
      exact Litex.inOfSame _litex_return_call _litex_return_call _value_i3 _value_i3 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _value_i3) (Litex.callOnInOutput _litex_return_call)))) True.intro))
  exact (by
    let _equal_wd_1_0 := _object_w11
    let _equal_wd_1_1 := _object_w12
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_20 _Host_i2 _rep_i2 _value_i2 h_21 _Host_i3 _rep_i3 _value_i3 h_22 _Host_i4 _rep_i4 _value_i4 h_24 _Host_i6 _rep_i6 _value_i6 h_27 _Host_i9 _rep_i9 _value_i9 h_28 h_1
          let _object_w11 := (let h_173 : Litex.In _value_i1 (Litex.Z (M := M)) := h_20;
          let h_178 : Litex.In _value_i2 (Litex.Z (M := M)) := h_21;
          let h_185 : Litex.In _value_i9 _value_i3 := h_28;
          Litex.rangeFold _value_i1 _value_i2 _value_i4 _value_i6 _value_i9 (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) h_173 h_178 (Litex.inOfSame _value_i4 _value_i4 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input))) (Litex.sameRefl _value_i4) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)))) h_24) (Litex.inOfSame _value_i6 _value_i6 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
            have _finiteProof_0 := (Litex.isSet _value_i3)
            have _finiteProof_1 := (Litex.isSet _value_i3)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
            have _finiteProof_0 := (Litex.isSet _value_i3)
            have _finiteProof_1 := (Litex.isSet _value_i3)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.sameRefl _value_i6) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
            have _finiteProof_0 := (Litex.isSet _value_i3)
            have _finiteProof_1 := (Litex.isSet _value_i3)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))) h_27) h_185 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.Z (M := M))) (Litex.denote _value_i3) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _value_i3) (fun (_raw_i5 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩))
          let _object_w12 := (let _object_w5 := (let _wd_2_0 := _value_i1;
          let _wd_2_1 := (Litex.sub _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i2 h_21) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_2_2 := _value_i4;
          let _wd_2_3 := _value_i6;
          let _wd_2_4 := _value_i9;
          (let h_237 : Litex.In _wd_2_0 (Litex.Z (M := M)) := h_20;
          let h_242 : (by
            let _atomic_wd_1_0 := _wd_2_1
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) := (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.subInZ _value_i2 (Litex.number (M := M) (1 : ℂ)) h_21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))));
          let h_313 : Litex.In _wd_2_4 _value_i3 := h_28;
          Litex.rangeFold _wd_2_0 _wd_2_1 _wd_2_2 _wd_2_3 _wd_2_4 (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) h_237 h_242 (Litex.inOfSame _wd_2_2 _wd_2_2 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input))) (Litex.sameRefl _wd_2_2) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)))) h_24) (Litex.inOfSame _wd_2_3 _wd_2_3 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
            have _finiteProof_0 := (Litex.isSet _value_i3)
            have _finiteProof_1 := (Litex.isSet _value_i3)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
            have _finiteProof_0 := (Litex.isSet _value_i3)
            have _finiteProof_1 := (Litex.isSet _value_i3)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.sameRefl _wd_2_3) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
            have _finiteProof_0 := (Litex.isSet _value_i3)
            have _finiteProof_1 := (Litex.isSet _value_i3)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))) h_27) h_313 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.Z (M := M))) (Litex.denote _value_i3) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _value_i3) (fun (_raw_i5 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)));
          let _object_w6 := (let _litex_call_arg_0 := _value_i2;
          Litex.callOnDomain (Litex.Z (M := M)) _value_i3 (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_24 h_21 True.intro);
          (let _litex_call_arg_0 := _object_w5;
          let _litex_call_arg_1 := _object_w6;
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
            have _finiteProof_0 := (Litex.isSet _value_i3)
            have _finiteProof_1 := (Litex.isSet _value_i3)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) _value_i3 (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i6 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_27 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_0 := _object_w5
            exact (by
              have _selected_operation : Litex.In _value_i6 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
              have _finiteProof_0 := (Litex.isSet _value_i3)
              have _finiteProof_1 := (Litex.isSet _value_i3)
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) := h_27
              exact Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 _value_i3 _value_i3 (Litex.sameRefl _atomic_wd_1_0) (Litex.sameRefl _value_i3) (Litex.rangeFoldInOutput _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _object_w6
            exact (by
              let _litex_return_call := _object_w6
              exact Litex.inOfSame _litex_return_call _litex_return_call _value_i3 _value_i3 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _value_i3) (Litex.callOnInOutput _litex_return_call)))) True.intro))
          have h_2 : (by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w11;
                  let _equal_wd_1_1 := _object_w12;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    have h_386 : Litex.Le _value_i1 _value_i2 := h_1
                    have h_391 : (by
                    let _equal_wd_2_0 := ((_equal_wd_1_1).val.argument.val.first).val.last
                    let _equal_wd_2_1 := _equal_wd_2_0
                    exact Litex.Same _equal_wd_2_1 _equal_wd_2_1) := (show @Eq M.Value _ _ from Eq.refl _)
                    have h_471 : (by
                    let _equal_wd_2_0 := (let _object_w7 := (let _wd_2_0 := _value_i1;
                    let _wd_2_1 := ((_equal_wd_1_1).val.argument.val.first).val.last;
                    let _wd_2_2 := _value_i4;
                    let _wd_2_3 := _value_i6;
                    let _wd_2_4 := _value_i9;
                    (let h_511 : Litex.In _wd_2_0 (Litex.Z (M := M)) := h_20;
                    let h_516 : (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) := (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (Litex.subInZ _value_i2 (Litex.number (M := M) (1 : ℂ)) h_21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))));
                    let h_587 : Litex.In _wd_2_4 _value_i3 := h_28;
                    Litex.rangeFold _wd_2_0 _wd_2_1 _wd_2_2 _wd_2_3 _wd_2_4 (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) h_511 h_516 (Litex.inOfSame _wd_2_2 _wd_2_2 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input))) (Litex.sameRefl _wd_2_2) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)))) h_24) (Litex.inOfSame _wd_2_3 _wd_2_3 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
                      have _finiteProof_0 := (Litex.isSet _value_i3)
                      have _finiteProof_1 := (Litex.isSet _value_i3)
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
                      have _finiteProof_0 := (Litex.isSet _value_i3)
                      have _finiteProof_1 := (Litex.isSet _value_i3)
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.sameRefl _wd_2_3) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
                      have _finiteProof_0 := (Litex.isSet _value_i3)
                      have _finiteProof_1 := (Litex.isSet _value_i3)
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))) h_27) h_587 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.Z (M := M))) (Litex.denote _value_i3) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _value_i3) (fun (_raw_i5 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)));
                    let _object_w8 := (_equal_wd_1_1).val.argument.val.second;
                    (let _litex_call_arg_0 := _object_w7;
                    let _litex_call_arg_1 := _object_w8;
                    Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
                      have _finiteProof_0 := (Litex.isSet _value_i3)
                      have _finiteProof_1 := (Litex.isSet _value_i3)
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) _value_i3 (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i6 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_27 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                      let _atomic_wd_1_0 := _object_w7
                      exact (by
                        have _selected_operation : Litex.In _value_i6 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
                        have _finiteProof_0 := (Litex.isSet _value_i3)
                        have _finiteProof_1 := (Litex.isSet _value_i3)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) := h_27
                        exact Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 _value_i3 _value_i3 (Litex.sameRefl _atomic_wd_1_0) (Litex.sameRefl _value_i3) (Litex.rangeFoldInOutput _atomic_wd_1_0))) (by
                      let _atomic_wd_1_0 := _object_w8
                      exact (by
                        let _litex_return_call := _object_w8
                        exact Litex.inOfSame _litex_return_call _litex_return_call _value_i3 _value_i3 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _value_i3) (Litex.callOnInOutput _litex_return_call)))) True.intro))
                    let _equal_wd_2_1 := (let _object_w9 := (let _wd_2_0 := _value_i1;
                    let _wd_2_1 := ((_equal_wd_2_0).val.argument.val.first).val.last;
                    let _wd_2_2 := _value_i4;
                    let _wd_2_3 := _value_i6;
                    let _wd_2_4 := _value_i9;
                    (let h_697 : Litex.In _wd_2_0 (Litex.Z (M := M)) := h_20;
                    let h_702 : (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) := (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (Litex.subInZ _value_i2 (Litex.number (M := M) (1 : ℂ)) h_21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))));
                    let h_773 : Litex.In _wd_2_4 _value_i3 := h_28;
                    Litex.rangeFold _wd_2_0 _wd_2_1 _wd_2_2 _wd_2_3 _wd_2_4 (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) h_697 h_702 (Litex.inOfSame _wd_2_2 _wd_2_2 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input))) (Litex.sameRefl _wd_2_2) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)))) h_24) (Litex.inOfSame _wd_2_3 _wd_2_3 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
                      have _finiteProof_0 := (Litex.isSet _value_i3)
                      have _finiteProof_1 := (Litex.isSet _value_i3)
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
                      have _finiteProof_0 := (Litex.isSet _value_i3)
                      have _finiteProof_1 := (Litex.isSet _value_i3)
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.sameRefl _wd_2_3) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
                      have _finiteProof_0 := (Litex.isSet _value_i3)
                      have _finiteProof_1 := (Litex.isSet _value_i3)
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))) h_27) h_773 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.Z (M := M))) (Litex.denote _value_i3) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _value_i3) (fun (_raw_i5 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)));
                    let _object_w10 := (_equal_wd_2_0).val.argument.val.second;
                    (let _litex_call_arg_0 := _object_w9;
                    let _litex_call_arg_1 := _object_w10;
                    Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
                      have _finiteProof_0 := (Litex.isSet _value_i3)
                      have _finiteProof_1 := (Litex.isSet _value_i3)
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) _value_i3 (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i6 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_27 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                      let _atomic_wd_1_0 := _object_w9
                      exact (by
                        have _selected_operation : Litex.In _value_i6 (Litex.fnSet (let _litex_output := _value_i3; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i3), (Litex.denote _value_i3)] (by
                        have _finiteProof_0 := (Litex.isSet _value_i3)
                        have _finiteProof_1 := (Litex.isSet _value_i3)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) := h_27
                        exact Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 _value_i3 _value_i3 (Litex.sameRefl _atomic_wd_1_0) (Litex.sameRefl _value_i3) (Litex.rangeFoldInOutput _atomic_wd_1_0))) (by
                      let _atomic_wd_1_0 := _object_w10
                      exact (by
                        let _litex_return_call := _object_w10
                        exact Litex.inOfSame _litex_return_call _litex_return_call _value_i3 _value_i3 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _value_i3) (Litex.callOnInOutput _litex_return_call)))) True.intro))
                    exact Litex.Same _equal_wd_2_1 _equal_wd_2_1) := (show @Eq M.Value _ _ from Eq.refl _)
                    have _endpoint : (M.subValue (Litex.denote _value_i2) (M.number (1 : ℂ))) = (M.subValue (Litex.denote _value_i2) (M.number (1 : ℂ))) := h_391
                    have _step : Litex.Same _equal_wd_1_0 _equal_wd_1_1 := by
                      change (Litex.rangeFoldValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i4) (Litex.denote _value_i6) (Litex.denote _value_i9)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i6) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.rangeFoldValue (M := M) (Litex.denote _value_i1) (M.subValue (Litex.denote _value_i2) (M.number (1 : ℂ))) (Litex.denote _value_i4) (Litex.denote _value_i6) (Litex.denote _value_i9)), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.denote _value_i2))]))
                      have _last := Litex.rangeFoldLast _equal_wd_1_0 h_386
                      change (Litex.rangeFoldValue (M := M) (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i4) (Litex.denote _value_i6) (Litex.denote _value_i9)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i6) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.rangeFoldValue (M := M) (Litex.denote _value_i1) (M.subValue (Litex.denote _value_i2) (M.number (1 : ℂ))) (Litex.denote _value_i4) (Litex.denote _value_i6) (Litex.denote _value_i9)), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.denote _value_i2))])) at _last
                      simpa only [_endpoint] using _last
                    exact (_step.trans h_471))))
                )
            )
          exact h_2
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_fold_x5f_last_x5f_step_x2f_statement_x2e_lit
