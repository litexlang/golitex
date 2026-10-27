import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_fold_x5f_carrier_x2f_statement_x2e_lit

universe u v1 v2 v3 v6 v8 v9 v10 v11 v12 v13
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_7 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_11 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_12 : Litex.IsFiniteSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_15 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → M.mem _raw_i5 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → True := (by
    intro _raw_i4 _raw_i5 h_13 h_14 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_13)
    have h_13 : Litex.In _value_i4 _value_i1 := h_13
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i5 _value_i1 := h_14
    exact True.intro);
  Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
  have _finiteProof_0 := (Litex.isSet _value_i1)
  have _finiteProof_1 := (Litex.isSet _value_i1)
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_17 : Litex.In _value_i6 (let _checked_header : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _value_i1) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → True := (by
    intro _raw_i7 h_16 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_16)
    have h_16 : Litex.In _value_i7 _value_i1 := h_16
    exact True.intro);
  Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_18 : Litex.In _value_i8 _value_i1) (h_1 : Litex.Subset _value_i2 _value_i1) (h_3 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_26 : Litex.In _value_i9 _value_i1) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_27 : Litex.In _value_i10 _value_i1), (by
  let _equal_wd_1_0 := (let _litex_call_arg_0 := _value_i9;
  let _litex_call_arg_1 := _value_i10;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_26 h_27) True.intro)
  let _equal_wd_1_1 := (let _litex_call_arg_0 := _value_i10;
  let _litex_call_arg_1 := _value_i9;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_27 h_26) True.intro)
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) (h_5 : ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_52 : Litex.In _value_i11 _value_i1) {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_53 : Litex.In _value_i12 _value_i1) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_54 : Litex.In _value_i13 _value_i1), (by
  let _equal_wd_1_0 := (let _object_w3 := (let _litex_call_arg_0 := _value_i11;
  let _litex_call_arg_1 := _value_i12;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_52 h_53) True.intro);
  let _wd_1_1 := _value_i13;
  (let _litex_call_arg_0 := _object_w3;
  let _litex_call_arg_1 := _wd_1_1;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_0 := _object_w3
    exact (by
      let _litex_return_call := _object_w3
      exact Litex.inOfSame _litex_return_call _litex_return_call _value_i1 _value_i1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _value_i1) (Litex.callOnInOutput _litex_return_call))) h_54) True.intro))
  let _equal_wd_1_1 := (let _wd_1_0 := _value_i11;
  let _object_w4 := (let _litex_call_arg_0 := _value_i12;
  let _litex_call_arg_1 := _value_i13;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_53 h_54) True.intro);
  (let _litex_call_arg_0 := _wd_1_0;
  let _litex_call_arg_1 := _object_w4;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_52 (by
    let _atomic_wd_1_0 := _object_w4
    exact (by
      let _litex_return_call := _object_w4
      exact Litex.inOfSame _litex_return_call _litex_return_call _value_i1 _value_i1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _value_i1) (Litex.callOnInOutput _litex_return_call)))) True.intro))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), (by
  let _object_w7 := (let h_167 : Litex.IsFiniteSet _value_i2 := h_12;
  let h_170 : Litex.In _value_i8 _value_i1 := h_18;
  let h_180 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_182 : Litex.In _value_i15 _value_i1) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_183 : Litex.In _value_i16 _value_i1), Litex.Same (let _litex_call_arg_0 := _value_i15;
  let _litex_call_arg_1 := _value_i16;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_182 h_183) True.intro) (let _litex_call_arg_0 := _value_i16;
  let _litex_call_arg_1 := _value_i15;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_183 h_182) True.intro) := (by
    intro _Host_i15 _rep_i15 _value_i15 h_182 _Host_i16 _rep_i16 _value_i16 h_183
    exact (h_3 _value_i15 h_182 _value_i16 h_183)
  );
  let h_209 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_211 : Litex.In _value_i15 _value_i1) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_212 : Litex.In _value_i16 _value_i1) {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_213 : Litex.In _value_i17 _value_i1), Litex.Same (let _object_w5 := (let _litex_call_arg_0 := _value_i15;
  let _litex_call_arg_1 := _value_i16;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_211 h_212) True.intro);
  let _wd_1_1 := _value_i17;
  (let _litex_call_arg_0 := _object_w5;
  let _litex_call_arg_1 := _wd_1_1;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_0 := _object_w5
    exact (by
      let _litex_return_call := _object_w5
      exact Litex.inOfSame _litex_return_call _litex_return_call _value_i1 _value_i1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _value_i1) (Litex.callOnInOutput _litex_return_call))) h_213) True.intro)) (let _wd_1_0 := _value_i15;
  let _object_w6 := (let _litex_call_arg_0 := _value_i16;
  let _litex_call_arg_1 := _value_i17;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_212 h_213) True.intro);
  (let _litex_call_arg_0 := _wd_1_0;
  let _litex_call_arg_1 := _object_w6;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_211 (by
    let _atomic_wd_1_0 := _object_w6
    exact (by
      let _litex_return_call := _object_w6
      exact Litex.inOfSame _litex_return_call _litex_return_call _value_i1 _value_i1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _value_i1) (Litex.callOnInOutput _litex_return_call)))) True.intro)) := (by
    intro _Host_i15 _rep_i15 _value_i15 h_211 _Host_i16 _rep_i16 _value_i16 h_212 _Host_i17 _rep_i17 _value_i17 h_213
    exact (h_5 _value_i15 h_211 _value_i16 h_212 _value_i17 h_213)
  );
  let h_326 : Litex.Subset _value_i2 _value_i1 := h_1;
  Litex.finiteFold _value_i2 _value_i6 _value_i3 _value_i8 (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) h_167 (Litex.inOfSame _value_i6 _value_i6 (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input))) (Litex.sameRefl _value_i6) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)))) h_17) (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))) h_15) h_170 (fun i hi => (Litex.FunctionSignature.withGuard_domain (Litex.denote _value_i1) (Litex.denote _value_i1) (Litex.isSet _value_i1) (Litex.isSet _value_i1) (fun (_raw_i7 : M.Value) => True) i).mpr ⟨h_326 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} _value_i1 (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} _value_i1 (fun _fold_x1 _fold_h1 => (h_180 _fold_x0 _fold_h0 _fold_x1 _fold_h1))))) (Litex.forallMembersOfRepresentations.{u, _, 0} _value_i1 (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} _value_i1 (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} _value_i1 (fun _fold_x2 _fold_h2 => (h_209 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))
  exact (by
    let _atomic_wd_1_0 := _object_w7
    exact Litex.In _atomic_wd_1_0 _value_i1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_11 _Host_i2 _rep_i2 _value_i2 h_12 _Host_i3 _rep_i3 _value_i3 h_15 _Host_i6 _rep_i6 _value_i6 h_17 _Host_i8 _rep_i8 _value_i8 h_18 h_1 h_3 h_5
          let _object_w7 := (let h_167 : Litex.IsFiniteSet _value_i2 := h_12;
          let h_170 : Litex.In _value_i8 _value_i1 := h_18;
          let h_180 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_182 : Litex.In _value_i15 _value_i1) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_183 : Litex.In _value_i16 _value_i1), Litex.Same (let _litex_call_arg_0 := _value_i15;
          let _litex_call_arg_1 := _value_i16;
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
            have _finiteProof_0 := (Litex.isSet _value_i1)
            have _finiteProof_1 := (Litex.isSet _value_i1)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_182 h_183) True.intro) (let _litex_call_arg_0 := _value_i16;
          let _litex_call_arg_1 := _value_i15;
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
            have _finiteProof_0 := (Litex.isSet _value_i1)
            have _finiteProof_1 := (Litex.isSet _value_i1)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_183 h_182) True.intro) := (by
            intro _Host_i15 _rep_i15 _value_i15 h_182 _Host_i16 _rep_i16 _value_i16 h_183
            exact (h_3 _value_i15 h_182 _value_i16 h_183)
          );
          let h_209 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_211 : Litex.In _value_i15 _value_i1) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_212 : Litex.In _value_i16 _value_i1) {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_213 : Litex.In _value_i17 _value_i1), Litex.Same (let _object_w5 := (let _litex_call_arg_0 := _value_i15;
          let _litex_call_arg_1 := _value_i16;
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
            have _finiteProof_0 := (Litex.isSet _value_i1)
            have _finiteProof_1 := (Litex.isSet _value_i1)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_211 h_212) True.intro);
          let _wd_1_1 := _value_i17;
          (let _litex_call_arg_0 := _object_w5;
          let _litex_call_arg_1 := _wd_1_1;
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
            have _finiteProof_0 := (Litex.isSet _value_i1)
            have _finiteProof_1 := (Litex.isSet _value_i1)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_0 := _object_w5
            exact (by
              let _litex_return_call := _object_w5
              exact Litex.inOfSame _litex_return_call _litex_return_call _value_i1 _value_i1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _value_i1) (Litex.callOnInOutput _litex_return_call))) h_213) True.intro)) (let _wd_1_0 := _value_i15;
          let _object_w6 := (let _litex_call_arg_0 := _value_i16;
          let _litex_call_arg_1 := _value_i17;
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
            have _finiteProof_0 := (Litex.isSet _value_i1)
            have _finiteProof_1 := (Litex.isSet _value_i1)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_212 h_213) True.intro);
          (let _litex_call_arg_0 := _wd_1_0;
          let _litex_call_arg_1 := _object_w6;
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
            have _finiteProof_0 := (Litex.isSet _value_i1)
            have _finiteProof_1 := (Litex.isSet _value_i1)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_15 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_211 (by
            let _atomic_wd_1_0 := _object_w6
            exact (by
              let _litex_return_call := _object_w6
              exact Litex.inOfSame _litex_return_call _litex_return_call _value_i1 _value_i1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _value_i1) (Litex.callOnInOutput _litex_return_call)))) True.intro)) := (by
            intro _Host_i15 _rep_i15 _value_i15 h_211 _Host_i16 _rep_i16 _value_i16 h_212 _Host_i17 _rep_i17 _value_i17 h_213
            exact (h_5 _value_i15 h_211 _value_i16 h_212 _value_i17 h_213)
          );
          let h_326 : Litex.Subset _value_i2 _value_i1 := h_1;
          Litex.finiteFold _value_i2 _value_i6 _value_i3 _value_i8 (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)) h_167 (Litex.inOfSame _value_i6 _value_i6 (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input))) (Litex.sameRefl _value_i6) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)))) h_17) (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
            have _finiteProof_0 := (Litex.isSet _value_i1)
            have _finiteProof_1 := (Litex.isSet _value_i1)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
            have _finiteProof_0 := (Litex.isSet _value_i1)
            have _finiteProof_1 := (Litex.isSet _value_i1)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
            have _finiteProof_0 := (Litex.isSet _value_i1)
            have _finiteProof_1 := (Litex.isSet _value_i1)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))) h_15) h_170 (fun i hi => (Litex.FunctionSignature.withGuard_domain (Litex.denote _value_i1) (Litex.denote _value_i1) (Litex.isSet _value_i1) (Litex.isSet _value_i1) (fun (_raw_i7 : M.Value) => True) i).mpr ⟨h_326 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} _value_i1 (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} _value_i1 (fun _fold_x1 _fold_h1 => (h_180 _fold_x0 _fold_h0 _fold_x1 _fold_h1))))) (Litex.forallMembersOfRepresentations.{u, _, 0} _value_i1 (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} _value_i1 (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} _value_i1 (fun _fold_x2 _fold_h2 => (h_209 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))
          have h_6 : (by
            let _atomic_wd_1_0 := _object_w7
            exact Litex.In _atomic_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w7
                    exact (by
                      have _selected_operation : Litex.In _value_i3 (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
                      have _finiteProof_0 := (Litex.isSet _value_i1)
                      have _finiteProof_1 := (Litex.isSet _value_i1)
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) := h_15
                      exact Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 _value_i1 _value_i1 (Litex.sameRefl _atomic_wd_1_0) (Litex.sameRefl _value_i1) (Litex.finiteFoldInOutput _atomic_wd_1_0)))
                )
            )
          exact h_6
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_fold_x5f_carrier_x2f_statement_x2e_lit
