import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_fold_x5f_carrier_x2f_statement_x2e_lit

universe u v1 v2 v4 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote (Litex.Z (M := M))) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_8 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_8)
    have h_8 : Litex.In _value_i3 (Litex.Z (M := M)) := h_8
    exact True.intro);
  Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_12 : Litex.In _value_i4 (let _checked_header : ∀ (_raw_i5 : M.Value) (_raw_i6 : M.Value), M.mem _raw_i5 (Litex.denote _value_i1) → M.mem _raw_i6 (Litex.denote _value_i1) → ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _raw_i5 _raw_i6) → True := (by
    intro _raw_i5 _raw_i6 h_10 h_11 _
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_10)
    have h_10 : Litex.In _value_i5 _value_i1 := h_10
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_11)
    have h_11 : Litex.In _value_i6 _value_i1 := h_11
    exact True.intro);
  Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
  have _finiteProof_0 := (Litex.isSet _value_i1)
  have _finiteProof_1 := (Litex.isSet _value_i1)
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_13 : Litex.In _value_i7 _value_i1), (by
  let _object_w5 := (let h_14 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
  let h_21 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
  let h_28 : Litex.In _value_i7 _value_i1 := h_13;
  Litex.rangeFold (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) _value_i2 _value_i4 _value_i7 (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) h_14 h_21 (Litex.inOfSame _value_i2 _value_i2 (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input))) (Litex.sameRefl _value_i2) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)))) h_9) (Litex.inOfSame _value_i4 _value_i4 (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.sameRefl _value_i4) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
    have _finiteProof_0 := (Litex.isSet _value_i1)
    have _finiteProof_1 := (Litex.isSet _value_i1)
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))) h_12) h_28 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.Z (M := M))) (Litex.denote _value_i1) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _value_i1) (fun (_raw_i3 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩))
  exact (by
    let _atomic_wd_1_0 := _object_w5
    exact Litex.In _atomic_wd_1_0 _value_i1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 _Host_i2 _rep_i2 _value_i2 h_9 _Host_i4 _rep_i4 _value_i4 h_12 _Host_i7 _rep_i7 _value_i7 h_13
          let _object_w5 := (let h_14 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
          let h_21 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
          let h_28 : Litex.In _value_i7 _value_i1 := h_13;
          Litex.rangeFold (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) _value_i2 _value_i4 _value_i7 (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) h_14 h_21 (Litex.inOfSame _value_i2 _value_i2 (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input))) (Litex.sameRefl _value_i2) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.Z (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)))) h_9) (Litex.inOfSame _value_i4 _value_i4 (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
            have _finiteProof_0 := (Litex.isSet _value_i1)
            have _finiteProof_1 := (Litex.isSet _value_i1)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
            have _finiteProof_0 := (Litex.isSet _value_i1)
            have _finiteProof_1 := (Litex.isSet _value_i1)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) (Litex.sameRefl _value_i4) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
            have _finiteProof_0 := (Litex.isSet _value_i1)
            have _finiteProof_1 := (Litex.isSet _value_i1)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))) h_12) h_28 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.Z (M := M))) (Litex.denote _value_i1) (Litex.isSet (Litex.Z (M := M))) (Litex.isSet _value_i1) (fun (_raw_i3 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w5
            exact Litex.In _atomic_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    exact (by
                      have _selected_operation : Litex.In _value_i4 (Litex.fnSet (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote _value_i1), (Litex.denote _value_i1)] (by
                      have _finiteProof_0 := (Litex.isSet _value_i1)
                      have _finiteProof_1 := (Litex.isSet _value_i1)
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) := h_12
                      exact Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 _value_i1 _value_i1 (Litex.sameRefl _atomic_wd_1_0) (Litex.sameRefl _value_i1) (Litex.rangeFoldInOutput _atomic_wd_1_0)))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_fold_x5f_carrier_x2f_statement_x2e_lit
