import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_outer_x5f_transpose_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_14 : Litex.In _value_i3 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_24 : Litex.In _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_6)), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _value_i1 _value_i2 h_4 h_6 (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)
    exact h_14) (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_6)
    exact h_24));
  let _wd_1_1 := _value_i1;
  let _wd_1_2 := _value_i2;
  (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_4 h_6 (by
    let _atomic_wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _wd_1_1 _wd_1_2 h_4 h_6 (by
      let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)
      exact h_14) (by
      let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_6)
      exact h_24))
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)
    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixOuterInFnSet _litex_matrix))))))
  let _equal_wd_1_1 := (Litex.matrixOuter _value_i4 _value_i3 _value_i2 _value_i1 h_6 h_4 (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_6)
    exact h_24) (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)
    exact h_14))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_6 _Host_i3 _rep_i3 _value_i3 h_14 _Host_i4 _rep_i4 _value_i4 h_24
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
          let _object_h15 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)))
          have h_15 : Litex.In _value_i3 _object_h15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4) _object_h15 (Litex.sameRefl _value_i3) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)) h_14)
                )
            )
          let _object_h25 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_6)))
          have h_25 : Litex.In _value_i4 _object_h25 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_6) _object_h25 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_6)) h_24)
                )
            )
          have h_255 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have h_257 : Litex.In _value_i2 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_265 : Litex.In _value_i3 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255) :=
            (by
              litex_checked_step =>
                exact (
                  h_14
                )
            )
          have h_275 : Litex.In _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257) :=
            (by
              litex_checked_step =>
                exact (
                  h_24
                )
            )
          have h_256 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_255)
                )
            )
          have h_258 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_257)
                )
            )
          let _object_h266 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)))
          have h_266 : Litex.In _value_i3 _object_h266 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255) _object_h266 (Litex.sameRefl _value_i3) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)) h_265)
                )
            )
          let _object_h276 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)))
          have h_276 : Litex.In _value_i4 _object_h276 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257) _object_h276 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)) h_275)
                )
            )
          have h_277 : Litex.Same (let _wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _value_i1 _value_i2 h_255 h_257 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
            exact h_265) (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
            exact h_275));
          let _wd_1_1 := _value_i1;
          let _wd_1_2 := _value_i2;
          (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_255 h_257 (by
            let _atomic_wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _wd_1_1 _wd_1_2 h_255 h_257 (by
              let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
              exact h_265) (by
              let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
              exact h_275))
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_255 h_257)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixOuterInFnSet _litex_matrix)))))) (Litex.matrixOuter _value_i4 _value_i3 _value_i2 _value_i1 h_257 h_255 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
            exact h_275) (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
            exact h_265)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _pointwise : ∀ {_Host_i97 : Type _} [_rep_i97 : Litex.Representation M _Host_i97] (_value_i97 : Litex.Obj (M := M) _Host_i97) (h_7973 : Litex.In _value_i97 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))) {_Host_i98 : Type _} [_rep_i98 : Litex.Representation M _Host_i98] (_value_i98 : Litex.Obj (M := M) _Host_i98) (h_8034 : Litex.In _value_i98 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255))), (by
                      let _object_w74 := (let _litex_matrix_head := (let _wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _value_i1 _value_i2 h_255 h_257 (by
                        let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                        exact h_265) (by
                        let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                        exact h_275));
                      let _wd_1_1 := _value_i1;
                      let _wd_1_2 := _value_i2;
                      (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_255 h_257 (by
                        let _atomic_wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _wd_1_1 _wd_1_2 h_255 h_257 (by
                          let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                          exact h_265) (by
                          let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                          exact h_275))
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_255 h_257)
                        exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixOuterInFnSet _litex_matrix))))));
                      (let _litex_call_arg_0 := _value_i97;
                      let _litex_call_arg_1 := _value_i98;
                      Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.transposeInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))
                        exact h_7973) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255))
                        exact h_8034)), True.intro⟩)))
                      let _object_w75 := (let _litex_matrix_head := (Litex.matrixOuter _value_i4 _value_i3 _value_i2 _value_i1 h_257 h_255 (by
                        let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                        exact h_275) (by
                        let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                        exact h_265));
                      (let _litex_call_arg_0 := _value_i97;
                      let _litex_call_arg_1 := _value_i98;
                      Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixOuterInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))
                        exact h_7973) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255))
                        exact h_8034)), True.intro⟩)))
                      exact (by
                        let _equal_wd_1_0 := _object_w74
                        let _equal_wd_1_1 := _object_w75
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
                    ) := (by
                      intro _Host_i97 _rep_i97 _value_i97 h_7973 _Host_i98 _rep_i98 _value_i98 h_8034
                      have h_7974 : Litex.In _value_i97 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257)) _value_i97 h_7973).1
                            )
                        )
                      have h_7975 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i97 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257)) _value_i97 h_7973).2.1
                            )
                        )
                      have h_7976 : Litex.Le _value_i97 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257)) _value_i97 h_7973).2.2
                            )
                        )
                      have h_7977 : Litex.In _value_i97 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257)) _value_i97 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_7973)
                            )
                        )
                      have h_8035 : Litex.In _value_i98 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)) _value_i98 h_8034).1
                            )
                        )
                      have h_8036 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i98 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)) _value_i98 h_8034).2.1
                            )
                        )
                      have h_8037 : Litex.Le _value_i98 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)) _value_i98 h_8034).2.2
                            )
                        )
                      have h_8038 : Litex.In _value_i98 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)) _value_i98 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_8034)
                            )
                        )
                      let _object_w74 := (let _litex_matrix_head := (let _wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _value_i1 _value_i2 h_255 h_257 (by
                        let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                        exact h_265) (by
                        let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                        exact h_275));
                      let _wd_1_1 := _value_i1;
                      let _wd_1_2 := _value_i2;
                      (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_255 h_257 (by
                        let _atomic_wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _wd_1_1 _wd_1_2 h_255 h_257 (by
                          let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                          exact h_265) (by
                          let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                          exact h_275))
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_255 h_257)
                        exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixOuterInFnSet _litex_matrix))))));
                      (let _litex_call_arg_0 := _value_i97;
                      let _litex_call_arg_1 := _value_i98;
                      Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.transposeInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))
                        exact h_7973) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255))
                        exact h_8034)), True.intro⟩)))
                      let _object_w75 := (let _litex_matrix_head := (Litex.matrixOuter _value_i4 _value_i3 _value_i2 _value_i1 h_257 h_255 (by
                        let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                        exact h_275) (by
                        let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                        exact h_265));
                      (let _litex_call_arg_0 := _value_i97;
                      let _litex_call_arg_1 := _value_i98;
                      Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixOuterInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))
                        exact h_7973) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255))
                        exact h_8034)), True.intro⟩)))
                      have h_7443 : (by
                        let _equal_wd_1_0 := _object_w74
                        let _equal_wd_1_1 := _object_w75
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (let _equal_wd_1_0 := _object_w74;
                              let _equal_wd_1_1 := _object_w75;
                              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show Litex.denote _equal_wd_1_0 = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i98) (Litex.denote _value_i97))) from by
                                have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i97 _value_i98))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.transposeCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i97 _value_i98)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              ))) (fun (_litex_input : M.Value) => (fun (_raw_i170 : M.Value) (_raw_i171 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i97 _value_i98))).mpr ⟨(Litex.callArguments2_mem_cart _value_i97 _value_i98 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))
                                exact h_7973) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255))
                                exact h_8034)), True.intro⟩))
                                change Litex.denote _equal_wd_1_0 = Litex.matrixTransposeBody (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i97) (Litex.denote _value_i98)) at h
                                dsimp only [Litex.matrixConjugateTransposeBody, Litex.matrixTransposeBody] at h
                                rw [Litex.FiniteFunction.unpack_pack2] at h
                                exact h).trans (let _matrix_reduction_call := (let _litex_matrix_head := (Litex.matrixOuter _value_i3 _value_i4 _value_i1 _value_i2 h_255 h_257 (by
                                let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                                exact h_265) (by
                                let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                                exact h_275));
                              (let _litex_call_arg_0 := _value_i98;
                              let _litex_call_arg_1 := _value_i97;
                              Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixOuterInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255))
                                exact h_8034) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))
                                exact h_7973)), True.intro⟩)));
                                (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i98) (Litex.denote _value_i97))) = Litex.denote _matrix_reduction_call from rfl).trans ((show Litex.denote _matrix_reduction_call = (M.mulValue (Litex.FunctionSemantics.callValue (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.left) (Litex.denote _value_i98)) (Litex.FunctionSemantics.callValue (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.right) (Litex.denote _value_i97))) from by
                                have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i98 _value_i97))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.matrixOuterCall ((_equal_wd_1_0).val.function).val.matrix (Litex.denote (Litex.callArguments2 _value_i98 _value_i97)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              ))) (fun (_litex_input : M.Value) => (fun (_raw_i176 : M.Value) (_raw_i177 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i98 _value_i97))).mpr ⟨(Litex.callArguments2_mem_cart _value_i98 _value_i97 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255))
                                exact h_8034) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))
                                exact h_7973)), True.intro⟩))
                                change Litex.denote _matrix_reduction_call = Litex.matrixOuterBody (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.left) (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.right) (Litex.FiniteFunction.pack2 (Litex.denote _value_i98) (Litex.denote _value_i97)) at h
                                dsimp only [Litex.matrixOuterBody] at h
                                rw [Litex.FiniteFunction.unpack_pack2] at h
                                exact h).trans (show (M.mulValue (Litex.FunctionSemantics.callValue (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.left) (Litex.denote _value_i98)) (Litex.FunctionSemantics.callValue (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.right) (Litex.denote _value_i97))) = (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i98)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.denote _value_i97))) from rfl)))).trans ((Eq.refl (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i98)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.denote _value_i97)))).trans (((let _equal_wd_2_0 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i98;
                              Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_266 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255))
                                exact h_8034) True.intro);
                              let _wd_1_1 := (let _litex_call_arg_0 := _value_i97;
                              Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_276 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))
                                exact h_7973) True.intro);
                              (Litex.mul _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_1_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_1_0 := _wd_1_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_1_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              let _equal_wd_2_1 := (let _wd_1_0 := (_equal_wd_2_0).val.right;
                              let _wd_1_1 := (_equal_wd_2_0).val.left;
                              (Litex.mul _wd_1_0 _wd_1_1 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (by
                                  let _litex_return_call := _atomic_wd_1_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
                                let _atomic_wd_1_0 := _wd_1_1
                                exact (by
                                  let _litex_return_call := _atomic_wd_1_0
                                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                              (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((let _litex_numeric_call := (_equal_wd_2_0).val.left;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) * (let _litex_numeric_call := (_equal_wd_2_0).val.right;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member)) ((let _litex_numeric_call := (_equal_wd_2_1).val.left;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) * (let _litex_numeric_call := (_equal_wd_2_1).val.right;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denoteMul (_equal_wd_2_0).val.left (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (let _litex_numeric_call := (_equal_wd_2_0).val.left;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (let _litex_numeric_call := (_equal_wd_2_0).val.right;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denoteMul (_equal_wd_2_1).val.left (_equal_wd_2_1).val.right (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (let _litex_numeric_call := (_equal_wd_2_1).val.left;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (let _litex_numeric_call := (_equal_wd_2_1).val.right;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (by ring!))))).trans ((let _matrix_beta_call := (let _litex_matrix_head := (Litex.matrixOuter _value_i4 _value_i3 _value_i2 _value_i1 h_257 h_255 (by
                                let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                                exact h_275) (by
                                let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                                exact h_265));
                              (let _litex_call_arg_0 := _value_i97;
                              let _litex_call_arg_1 := _value_i98;
                              Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixOuterInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))
                                exact h_7973) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255))
                                exact h_8034)), True.intro⟩)));
                                (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_equal_wd_1_1).val.function) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i97), (Litex.denote _value_i98)])) = Litex.denote _matrix_beta_call from rfl).trans ((show Litex.denote _matrix_beta_call = (M.mulValue (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_1).val.function).val.left) (Litex.denote _value_i97)) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_1).val.function).val.right) (Litex.denote _value_i98))) from by
                                have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i97 _value_i98))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.matrixOuterCall (_equal_wd_1_1).val.function (Litex.denote (Litex.callArguments2 _value_i97 _value_i98)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              ))) (fun (_litex_input : M.Value) => (fun (_raw_i197 : M.Value) (_raw_i198 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i97 _value_i98))).mpr ⟨(Litex.callArguments2_mem_cart _value_i97 _value_i98 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))
                                exact h_7973) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255))
                                exact h_8034)), True.intro⟩))
                                change Litex.denote _matrix_beta_call = Litex.matrixOuterBody (Litex.denote ((_equal_wd_1_1).val.function).val.left) (Litex.denote ((_equal_wd_1_1).val.function).val.right) (Litex.FiniteFunction.pack2 (Litex.denote _value_i97) (Litex.denote _value_i98)) at h
                                dsimp only [Litex.matrixOuterBody] at h
                                rw [Litex.FiniteFunction.unpack_pack2] at h
                                exact h).trans (show (M.mulValue (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_1).val.function).val.left) (Litex.denote _value_i97)) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_1).val.function).val.right) (Litex.denote _value_i98))) = (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.denote _value_i97)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i98))) from rfl)))).symm)))))
                            )
                        )
                      exact h_7443
                    )
                    apply Litex.functionExtOnDomain (let _wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _value_i1 _value_i2 h_255 h_257 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                      exact h_265) (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                      exact h_275));
                    let _wd_1_1 := _value_i1;
                    let _wd_1_2 := _value_i2;
                    (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_255 h_257 (by
                      let _atomic_wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _wd_1_1 _wd_1_2 h_255 h_257 (by
                        let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                        exact h_265) (by
                        let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                        exact h_275))
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_255 h_257)
                      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixOuterInFnSet _litex_matrix)))))) (Litex.matrixOuter _value_i4 _value_i3 _value_i2 _value_i1 h_257 h_255 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                      exact h_275) (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                      exact h_265)) (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i95 : M.Value) (_raw_i96 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i26 : M.Value) (_raw_i27 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (let _litex_matrix := (let _wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _value_i1 _value_i2 h_255 h_257 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                      exact h_265) (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                      exact h_275));
                    let _wd_1_1 := _value_i1;
                    let _wd_1_2 := _value_i2;
                    (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_255 h_257 (by
                      let _atomic_wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _wd_1_1 _wd_1_2 h_255 h_257 (by
                        let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                        exact h_265) (by
                        let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                        exact h_275))
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_255 h_257)
                      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixOuterInFnSet _litex_matrix)))))); let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInFnSet _litex_matrix)) (let _litex_matrix := (Litex.matrixOuter _value_i4 _value_i3 _value_i2 _value_i1 h_257 h_255 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                      exact h_275) (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                      exact h_265)); let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixOuterInFnSet _litex_matrix)) (by rfl)
                    intro _preimage_input _preimage_domain
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i95 : M.Value) (_raw_i96 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
                    have _preimage_base : M.mem _preimage_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_257))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_255)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
                      have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
                      have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))
                    have _repack : _preimage_input = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ)))]) := (by
                      apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
                      apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
                      funext i
                      fin_cases i <;> norm_num [Litex.FiniteFunction.index])
                    exact Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (let _wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _value_i1 _value_i2 h_255 h_257 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                      exact h_265) (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                      exact h_275));
                    let _wd_1_1 := _value_i1;
                    let _wd_1_2 := _value_i2;
                    (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_255 h_257 (by
                      let _atomic_wd_1_0 := (Litex.matrixOuter _value_i3 _value_i4 _wd_1_1 _wd_1_2 h_255 h_257 (by
                        let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                        exact h_265) (by
                        let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                        exact h_275))
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_255 h_257)
                      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixOuterInFnSet _litex_matrix))))))) x = Litex.FunctionSemantics.callValue (M := M) (Litex.denote (Litex.matrixOuter _value_i4 _value_i3 _value_i2 _value_i1 h_257 h_255 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_257)
                      exact h_275) (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_255)
                      exact h_265))) x) _repack) (_pointwise (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)) (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))
                  )
                )
            )
          exact h_277
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_outer_x5f_transpose_x2f_statement_x2e_lit
