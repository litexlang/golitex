import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_conjugate_x5f_transpose_x5f_involution_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_21 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.conjugateTranspose _value_i3 _value_i1 _value_i2 h_4 h_6 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)
    exact h_21));
  let _wd_1_1 := _value_i2;
  let _wd_1_2 := _value_i1;
  (Litex.conjugateTranspose _wd_1_0 _wd_1_1 _wd_1_2 h_6 h_4 (by
    let _atomic_wd_1_0 := (Litex.conjugateTranspose _value_i3 _wd_1_2 _wd_1_1 h_4 h_6 (by
      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)
      exact h_21))
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_6 h_4)
    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInFnSet _litex_matrix))))))
  exact Litex.Same _equal_wd_1_0 _value_i3) :=
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
          have h_200 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have h_202 : Litex.In _value_i2 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_217 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202) :=
            (by
              litex_checked_step =>
                exact (
                  h_21
                )
            )
          have h_201 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_200)
                )
            )
          have h_203 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_202)
                )
            )
          let _object_h218 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)))
          have h_218 : Litex.In _value_i3 _object_h218 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202) _object_h218 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202))) h_217)
                )
            )
          have h_219 : Litex.Same (let _wd_1_0 := (Litex.conjugateTranspose _value_i3 _value_i1 _value_i2 h_200 h_202 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
            exact h_217));
          let _wd_1_1 := _value_i2;
          let _wd_1_2 := _value_i1;
          (Litex.conjugateTranspose _wd_1_0 _wd_1_1 _wd_1_2 h_202 h_200 (by
            let _atomic_wd_1_0 := (Litex.conjugateTranspose _value_i3 _wd_1_2 _wd_1_1 h_200 h_202 (by
              let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
              exact h_217))
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_202 h_200)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInFnSet _litex_matrix)))))) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _pointwise : ∀ {_Host_i115 : Type _} [_rep_i115 : Litex.Representation M _Host_i115] (_value_i115 : Litex.Obj (M := M) _Host_i115) (h_5171 : Litex.In _value_i115 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))) {_Host_i116 : Type _} [_rep_i116 : Litex.Representation M _Host_i116] (_value_i116 : Litex.Obj (M := M) _Host_i116) (h_5223 : Litex.In _value_i116 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202))), (by
                      let _object_w64 := (let _litex_matrix_head := (let _wd_1_0 := (Litex.conjugateTranspose _value_i3 _value_i1 _value_i2 h_200 h_202 (by
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
                        exact h_217));
                      let _wd_1_1 := _value_i2;
                      let _wd_1_2 := _value_i1;
                      (Litex.conjugateTranspose _wd_1_0 _wd_1_1 _wd_1_2 h_202 h_200 (by
                        let _atomic_wd_1_0 := (Litex.conjugateTranspose _value_i3 _wd_1_2 _wd_1_1 h_200 h_202 (by
                          let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
                          exact h_217))
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_202 h_200)
                        exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInFnSet _litex_matrix))))));
                      (let _litex_call_arg_0 := _value_i115;
                      let _litex_call_arg_1 := _value_i116;
                      Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.conjugateTransposeInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))
                        exact h_5171) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202))
                        exact h_5223)), True.intro⟩)))
                      let _object_w65 := (let _litex_call_arg_0 := _value_i115;
                      let _litex_call_arg_1 := _value_i116;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_218 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))
                        exact h_5171) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202))
                        exact h_5223)) True.intro)
                      exact (by
                        let _equal_wd_1_0 := _object_w64
                        let _equal_wd_1_1 := _object_w65
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
                    ) := (by
                      intro _Host_i115 _rep_i115 _value_i115 h_5171 _Host_i116 _rep_i116 _value_i116 h_5223
                      have h_5172 : Litex.In _value_i115 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200)) _value_i115 h_5171).1
                            )
                        )
                      have h_5173 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i115 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200)) _value_i115 h_5171).2.1
                            )
                        )
                      have h_5174 : Litex.Le _value_i115 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200)) _value_i115 h_5171).2.2
                            )
                        )
                      have h_5175 : Litex.In _value_i115 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200)) _value_i115 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5171)
                            )
                        )
                      have h_5224 : Litex.In _value_i116 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)) _value_i116 h_5223).1
                            )
                        )
                      have h_5225 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i116 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)) _value_i116 h_5223).2.1
                            )
                        )
                      have h_5226 : Litex.Le _value_i116 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)) _value_i116 h_5223).2.2
                            )
                        )
                      have h_5227 : Litex.In _value_i116 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)) _value_i116 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5223)
                            )
                        )
                      let _object_w64 := (let _litex_matrix_head := (let _wd_1_0 := (Litex.conjugateTranspose _value_i3 _value_i1 _value_i2 h_200 h_202 (by
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
                        exact h_217));
                      let _wd_1_1 := _value_i2;
                      let _wd_1_2 := _value_i1;
                      (Litex.conjugateTranspose _wd_1_0 _wd_1_1 _wd_1_2 h_202 h_200 (by
                        let _atomic_wd_1_0 := (Litex.conjugateTranspose _value_i3 _wd_1_2 _wd_1_1 h_200 h_202 (by
                          let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
                          exact h_217))
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_202 h_200)
                        exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInFnSet _litex_matrix))))));
                      (let _litex_call_arg_0 := _value_i115;
                      let _litex_call_arg_1 := _value_i116;
                      Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.conjugateTransposeInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))
                        exact h_5171) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202))
                        exact h_5223)), True.intro⟩)))
                      let _object_w65 := (let _litex_call_arg_0 := _value_i115;
                      let _litex_call_arg_1 := _value_i116;
                      Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_218 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))
                        exact h_5171) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202))
                        exact h_5223)) True.intro)
                      have h_4772 : (by
                        let _equal_wd_1_0 := _object_w64
                        let _equal_wd_1_1 := _object_w65
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (let _equal_wd_1_0 := _object_w64;
                              let _equal_wd_1_1 := _object_w65;
                              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show Litex.denote _equal_wd_1_0 = (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i116) (Litex.denote _value_i115)))) from by
                                have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i115 _value_i116))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.conjugateTransposeCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i115 _value_i116)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              ))) (fun (_litex_input : M.Value) => (fun (_raw_i203 : M.Value) (_raw_i204 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i115 _value_i116))).mpr ⟨(Litex.callArguments2_mem_cart _value_i115 _value_i116 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))
                                exact h_5171) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202))
                                exact h_5223)), True.intro⟩))
                                change Litex.denote _equal_wd_1_0 = Litex.matrixConjugateTransposeBody (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i115) (Litex.denote _value_i116)) at h
                                dsimp only [Litex.matrixConjugateTransposeBody, Litex.matrixTransposeBody] at h
                                rw [Litex.FiniteFunction.unpack_pack2] at h
                                exact h).trans ((show (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i116) (Litex.denote _value_i115)))) = (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) (Litex.denote (let _litex_matrix_head := (Litex.conjugateTranspose _value_i3 _value_i1 _value_i2 h_200 h_202 (by
                                let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
                                exact h_217));
                              (let _litex_call_arg_0 := _value_i116;
                              let _litex_call_arg_1 := _value_i115;
                              Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.conjugateTransposeInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202))
                                exact h_5223) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))
                                exact h_5171)), True.intro⟩)))) from rfl).trans ((congrArg (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) (let _matrix_reduction_call := (let _litex_matrix_head := (Litex.conjugateTranspose _value_i3 _value_i1 _value_i2 h_200 h_202 (by
                                let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
                                exact h_217));
                              (let _litex_call_arg_0 := _value_i116;
                              let _litex_call_arg_1 := _value_i115;
                              Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.conjugateTransposeInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202))
                                exact h_5223) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))
                                exact h_5171)), True.intro⟩)));
                                (show (Litex.denote (let _litex_matrix_head := (Litex.conjugateTranspose _value_i3 _value_i1 _value_i2 h_200 h_202 (by
                                let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
                                exact h_217));
                              (let _litex_call_arg_0 := _value_i116;
                              let _litex_call_arg_1 := _value_i115;
                              Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.conjugateTransposeInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202))
                                exact h_5223) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))
                                exact h_5171)), True.intro⟩)))) = Litex.denote _matrix_reduction_call from rfl).trans ((show Litex.denote _matrix_reduction_call = (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i115) (Litex.denote _value_i116)))) from by
                                have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i116 _value_i115))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.conjugateTransposeCall ((_equal_wd_1_0).val.function).val.matrix (Litex.denote (Litex.callArguments2 _value_i116 _value_i115)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              ))) (fun (_litex_input : M.Value) => (fun (_raw_i211 : M.Value) (_raw_i212 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i116 _value_i115))).mpr ⟨(Litex.callArguments2_mem_cart _value_i116 _value_i115 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202))
                                exact h_5223) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))
                                exact h_5171)), True.intro⟩))
                                change Litex.denote _matrix_reduction_call = Litex.matrixConjugateTransposeBody (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i116) (Litex.denote _value_i115)) at h
                                dsimp only [Litex.matrixConjugateTransposeBody, Litex.matrixTransposeBody] at h
                                rw [Litex.FiniteFunction.unpack_pack2] at h
                                exact h).trans ((show (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i115) (Litex.denote _value_i116)))) = (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) (Litex.denote _equal_wd_1_1) from rfl).trans ((congrArg (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) (show (Litex.denote _equal_wd_1_1) = (Litex.denote _equal_wd_1_1) from rfl)).trans (show (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) (Litex.denote _equal_wd_1_1) = (Litex.denote (let _wd_1_0 := _equal_wd_1_1;
                              (Litex.conj _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_1_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))) from rfl)))))).trans (show (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) (Litex.denote (let _wd_1_0 := _equal_wd_1_1;
                              (Litex.conj _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_1_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))) = (Litex.denote (let _wd_1_0 := (let _wd_2_0 := _equal_wd_1_1;
                              (Litex.conj _wd_2_0 (by
                                let _atomic_wd_1_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_1_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              (Litex.conj _wd_1_0 (by
                                let _atomic_wd_1_0 := (let _wd_2_0 := (_wd_1_0).val.arg;
                                (Litex.conj _wd_2_0 (by
                                  let _atomic_wd_2_0 := _wd_2_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_2_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.conjInC _atomic_wd_1_0))))) from rfl)))).trans (let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := _equal_wd_1_1;
                              (Litex.conj _wd_2_0 (by
                                let _atomic_wd_1_0 := _wd_2_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_1_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              (Litex.conj _wd_1_0 (by
                                let _atomic_wd_1_0 := (let _wd_2_0 := (_wd_1_0).val.arg;
                                (Litex.conj _wd_2_0 (by
                                  let _atomic_wd_2_0 := _wd_2_0
                                  exact (by
                                    let _litex_return_call := _atomic_wd_2_0
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                                exact (Litex.conjInC _atomic_wd_1_0))));
                              let _equal_wd_2_1 := ((_equal_wd_2_0).val.arg).val.arg;
                              (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 (star ((star ((let _litex_numeric_call := ((_equal_wd_2_0).val.arg).val.arg;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member))))) (let _litex_numeric_call := _equal_wd_2_1;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) (let _complex := _equal_wd_2_0; Litex.denoteConjugate _complex (star ((let _litex_numeric_call := ((_equal_wd_2_0).val.arg).val.arg;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member))) (let _complex := (_equal_wd_2_0).val.arg; Litex.denoteConjugate _complex (let _litex_numeric_call := ((_equal_wd_2_0).val.arg).val.arg;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) (let _litex_numeric_call := ((_equal_wd_2_0).val.arg).val.arg;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member))) (let _litex_numeric_call := _equal_wd_2_1;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (by exact star_star _)))))))
                            )
                        )
                      exact h_4772
                    )
                    apply Litex.functionExtOnDomain (let _wd_1_0 := (Litex.conjugateTranspose _value_i3 _value_i1 _value_i2 h_200 h_202 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
                      exact h_217));
                    let _wd_1_1 := _value_i2;
                    let _wd_1_2 := _value_i1;
                    (Litex.conjugateTranspose _wd_1_0 _wd_1_1 _wd_1_2 h_202 h_200 (by
                      let _atomic_wd_1_0 := (Litex.conjugateTranspose _value_i3 _wd_1_2 _wd_1_1 h_200 h_202 (by
                        let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
                        exact h_217))
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_202 h_200)
                      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInFnSet _litex_matrix)))))) _value_i3 (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i113 : M.Value) (_raw_i114 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i25 : M.Value) (_raw_i26 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (let _litex_matrix := (let _wd_1_0 := (Litex.conjugateTranspose _value_i3 _value_i1 _value_i2 h_200 h_202 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
                      exact h_217));
                    let _wd_1_1 := _value_i2;
                    let _wd_1_2 := _value_i1;
                    (Litex.conjugateTranspose _wd_1_0 _wd_1_1 _wd_1_2 h_202 h_200 (by
                      let _atomic_wd_1_0 := (Litex.conjugateTranspose _value_i3 _wd_1_2 _wd_1_1 h_200 h_202 (by
                        let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
                        exact h_217))
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_202 h_200)
                      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInFnSet _litex_matrix)))))); let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInFnSet _litex_matrix)) (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202) (Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i25 : M.Value) (_raw_i26 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202))) h_217) (by rfl)
                    intro _preimage_input _preimage_domain
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i113 : M.Value) (_raw_i114 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
                    have _preimage_base : M.mem _preimage_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_200))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_202)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
                      have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
                      have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))
                    have _repack : _preimage_input = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ)))]) := (by
                      apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
                      apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
                      funext i
                      fin_cases i <;> norm_num [Litex.FiniteFunction.index])
                    exact Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (let _wd_1_0 := (Litex.conjugateTranspose _value_i3 _value_i1 _value_i2 h_200 h_202 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
                      exact h_217));
                    let _wd_1_1 := _value_i2;
                    let _wd_1_2 := _value_i1;
                    (Litex.conjugateTranspose _wd_1_0 _wd_1_1 _wd_1_2 h_202 h_200 (by
                      let _atomic_wd_1_0 := (Litex.conjugateTranspose _value_i3 _wd_1_2 _wd_1_1 h_200 h_202 (by
                        let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_200 h_202)
                        exact h_217))
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_202 h_200)
                      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInFnSet _litex_matrix))))))) x = Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) x) _repack) (_pointwise (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)) (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))
                  )
                )
            )
          exact h_219
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_conjugate_x5f_transpose_x5f_involution_x2f_statement_x2e_lit
