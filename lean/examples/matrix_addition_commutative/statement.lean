import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_addition_x5f_commutative_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_21 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_23 : Litex.In _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)), (by
  let _equal_wd_1_0 := (Litex.matrixEntrywise .add _value_i3 _value_i4 _value_i1 _value_i2 h_4 h_6 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)
    exact h_21) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)
    exact h_23))
  let _equal_wd_1_1 := (Litex.matrixEntrywise .add _value_i4 _value_i3 _value_i1 _value_i2 h_4 h_6 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)
    exact h_23) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)
    exact h_21))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_6 _Host_i3 _rep_i3 _value_i3 h_21 _Host_i4 _rep_i4 _value_i4 h_23
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
          let _object_h24 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6)))
          have h_24 : Litex.In _value_i4 _object_h24 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6) _object_h24 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_4 h_6))) h_23)
                )
            )
          have h_93 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have h_95 : Litex.In _value_i2 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_110 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95) :=
            (by
              litex_checked_step =>
                exact (
                  h_21
                )
            )
          have h_112 : Litex.In _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95) :=
            (by
              litex_checked_step =>
                exact (
                  h_23
                )
            )
          have h_94 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_93)
                )
            )
          have h_96 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_95)
                )
            )
          let _object_h111 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)))
          have h_111 : Litex.In _value_i3 _object_h111 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95) _object_h111 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95))) h_110)
                )
            )
          let _object_h113 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)))
          have h_113 : Litex.In _value_i4 _object_h113 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95) _object_h113 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95))) h_112)
                )
            )
          have h_114 : Litex.Same (Litex.matrixEntrywise .add _value_i3 _value_i4 _value_i1 _value_i2 h_93 h_95 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
            exact h_110) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
            exact h_112)) (Litex.matrixEntrywise .add _value_i4 _value_i3 _value_i1 _value_i2 h_93 h_95 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
            exact h_112) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
            exact h_110)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _pointwise : ∀ {_Host_i26 : Type _} [_rep_i26 : Litex.Representation M _Host_i26] (_value_i26 : Litex.Obj (M := M) _Host_i26) (h_6026 : Litex.In _value_i26 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))) {_Host_i27 : Type _} [_rep_i27 : Litex.Representation M _Host_i27] (_value_i27 : Litex.Obj (M := M) _Host_i27) (h_6088 : Litex.In _value_i27 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95))), (by
                      let _object_w51 := (let _litex_matrix_head := (Litex.matrixEntrywise .add _value_i3 _value_i4 _value_i1 _value_i2 h_93 h_95 (by
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                        exact h_110) (by
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                        exact h_112));
                      (let _litex_call_arg_0 := _value_i26;
                      let _litex_call_arg_1 := _value_i27;
                      Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixEntrywiseInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))
                        exact h_6026) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95))
                        exact h_6088)), True.intro⟩)))
                      let _object_w52 := (let _litex_matrix_head := (Litex.matrixEntrywise .add _value_i4 _value_i3 _value_i1 _value_i2 h_93 h_95 (by
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                        exact h_112) (by
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                        exact h_110));
                      (let _litex_call_arg_0 := _value_i26;
                      let _litex_call_arg_1 := _value_i27;
                      Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixEntrywiseInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))
                        exact h_6026) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95))
                        exact h_6088)), True.intro⟩)))
                      exact (by
                        let _equal_wd_1_0 := _object_w51
                        let _equal_wd_1_1 := _object_w52
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
                    ) := (by
                      intro _Host_i26 _rep_i26 _value_i26 h_6026 _Host_i27 _rep_i27 _value_i27 h_6088
                      have h_6027 : Litex.In _value_i26 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93)) _value_i26 h_6026).1
                            )
                        )
                      have h_6028 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i26 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93)) _value_i26 h_6026).2.1
                            )
                        )
                      have h_6029 : Litex.Le _value_i26 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93)) _value_i26 h_6026).2.2
                            )
                        )
                      have h_6030 : Litex.In _value_i26 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93)) _value_i26 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6026)
                            )
                        )
                      have h_6089 : Litex.In _value_i27 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)) _value_i27 h_6088).1
                            )
                        )
                      have h_6090 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i27 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)) _value_i27 h_6088).2.1
                            )
                        )
                      have h_6091 : Litex.Le _value_i27 _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)) _value_i27 h_6088).2.2
                            )
                        )
                      have h_6092 : Litex.In _value_i27 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)) _value_i27 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6088)
                            )
                        )
                      let _object_w51 := (let _litex_matrix_head := (Litex.matrixEntrywise .add _value_i3 _value_i4 _value_i1 _value_i2 h_93 h_95 (by
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                        exact h_110) (by
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                        exact h_112));
                      (let _litex_call_arg_0 := _value_i26;
                      let _litex_call_arg_1 := _value_i27;
                      Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixEntrywiseInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))
                        exact h_6026) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95))
                        exact h_6088)), True.intro⟩)))
                      let _object_w52 := (let _litex_matrix_head := (Litex.matrixEntrywise .add _value_i4 _value_i3 _value_i1 _value_i2 h_93 h_95 (by
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                        exact h_112) (by
                        let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                        exact h_110));
                      (let _litex_call_arg_0 := _value_i26;
                      let _litex_call_arg_1 := _value_i27;
                      Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixEntrywiseInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))
                        exact h_6026) (by
                        let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95))
                        exact h_6088)), True.intro⟩)))
                      have h_5497 : (by
                        let _equal_wd_1_0 := _object_w51
                        let _equal_wd_1_1 := _object_w52
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (let _equal_wd_1_0 := _object_w51;
                              let _equal_wd_1_1 := _object_w52;
                              (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show Litex.denote _equal_wd_1_0 = (M.addValue (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.left) (Litex.FiniteFunction.pack2 (Litex.denote _value_i26) (Litex.denote _value_i27))) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.right) (Litex.FiniteFunction.pack2 (Litex.denote _value_i26) (Litex.denote _value_i27)))) from by
                                have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i26 _value_i27))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.matrixEntrywiseCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i26 _value_i27)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              ))) (fun (_litex_input : M.Value) => (fun (_raw_i50 : M.Value) (_raw_i51 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i26 _value_i27))).mpr ⟨(Litex.callArguments2_mem_cart _value_i26 _value_i27 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))
                                exact h_6026) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95))
                                exact h_6088)), True.intro⟩))
                                change Litex.denote _equal_wd_1_0 = Litex.matrixEntrywiseBody .add (Litex.denote ((_equal_wd_1_0).val.function).val.left) (Litex.denote ((_equal_wd_1_0).val.function).val.right) (Litex.FiniteFunction.pack2 (Litex.denote _value_i26) (Litex.denote _value_i27)) at h
                                dsimp only [Litex.matrixEntrywiseBody] at h
                                rw [Litex.FiniteFunction.unpack_pack2] at h
                                exact h).trans (show (M.addValue (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.left) (Litex.FiniteFunction.pack2 (Litex.denote _value_i26) (Litex.denote _value_i27))) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.right) (Litex.FiniteFunction.pack2 (Litex.denote _value_i26) (Litex.denote _value_i27)))) = (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i26), (Litex.denote _value_i27)])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i26), (Litex.denote _value_i27)]))) from rfl)).trans ((Eq.refl (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i26), (Litex.denote _value_i27)])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i26), (Litex.denote _value_i27)])))).trans (((let _equal_wd_2_0 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i26;
                              let _litex_call_arg_1 := _value_i27;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_111 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))
                                exact h_6026) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95))
                                exact h_6088)) True.intro);
                              let _wd_1_1 := (let _litex_call_arg_0 := _value_i26;
                              let _litex_call_arg_1 := _value_i27;
                              Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_113 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))
                                exact h_6026) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95))
                                exact h_6088)) True.intro);
                              (Litex.add _wd_1_0 _wd_1_1 (by
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
                              (Litex.add _wd_1_0 _wd_1_1 (by
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
                              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (let _litex_numeric_call := (_equal_wd_2_0).val.right;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member)) ((let _litex_numeric_call := (_equal_wd_2_1).val.left;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (let _litex_numeric_call := (_equal_wd_2_1).val.right;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denoteAdd (_equal_wd_2_0).val.left (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (let _litex_numeric_call := (_equal_wd_2_0).val.left;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (let _litex_numeric_call := (_equal_wd_2_0).val.right;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (Litex.NativeBridge.denoteAdd (_equal_wd_2_1).val.left (_equal_wd_2_1).val.right (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (let _litex_numeric_call := (_equal_wd_2_1).val.left;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (let _litex_numeric_call := (_equal_wd_2_1).val.right;
                              let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (show Litex.In _litex_numeric_call Litex.C from (Litex.callOnInOutput _litex_numeric_call));
                              Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)) (by ring!))))).trans ((let _matrix_beta_call := (let _litex_matrix_head := (Litex.matrixEntrywise .add _value_i4 _value_i3 _value_i1 _value_i2 h_93 h_95 (by
                                let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                                exact h_112) (by
                                let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                                exact h_110));
                              (let _litex_call_arg_0 := _value_i26;
                              let _litex_call_arg_1 := _value_i27;
                              Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixEntrywiseInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))
                                exact h_6026) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95))
                                exact h_6088)), True.intro⟩)));
                                (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_equal_wd_1_1).val.function) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i26), (Litex.denote _value_i27)])) = Litex.denote _matrix_beta_call from rfl).trans ((show Litex.denote _matrix_beta_call = (M.addValue (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_1).val.function).val.left) (Litex.FiniteFunction.pack2 (Litex.denote _value_i26) (Litex.denote _value_i27))) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_1).val.function).val.right) (Litex.FiniteFunction.pack2 (Litex.denote _value_i26) (Litex.denote _value_i27)))) from by
                                have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i26 _value_i27))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.matrixEntrywiseCall (_equal_wd_1_1).val.function (Litex.denote (Litex.callArguments2 _value_i26 _value_i27)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              ))) (fun (_litex_input : M.Value) => (fun (_raw_i70 : M.Value) (_raw_i71 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i26 _value_i27))).mpr ⟨(Litex.callArguments2_mem_cart _value_i26 _value_i27 (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))
                                exact h_6026) (by
                                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95))
                                exact h_6088)), True.intro⟩))
                                change Litex.denote _matrix_beta_call = Litex.matrixEntrywiseBody .add (Litex.denote ((_equal_wd_1_1).val.function).val.left) (Litex.denote ((_equal_wd_1_1).val.function).val.right) (Litex.FiniteFunction.pack2 (Litex.denote _value_i26) (Litex.denote _value_i27)) at h
                                dsimp only [Litex.matrixEntrywiseBody] at h
                                rw [Litex.FiniteFunction.unpack_pack2] at h
                                exact h).trans (show (M.addValue (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_1).val.function).val.left) (Litex.FiniteFunction.pack2 (Litex.denote _value_i26) (Litex.denote _value_i27))) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_1).val.function).val.right) (Litex.FiniteFunction.pack2 (Litex.denote _value_i26) (Litex.denote _value_i27)))) = (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i4) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i26), (Litex.denote _value_i27)])) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i26), (Litex.denote _value_i27)]))) from rfl)))).symm)))))
                            )
                        )
                      exact h_5497
                    )
                    apply Litex.functionExtOnDomain (Litex.matrixEntrywise .add _value_i3 _value_i4 _value_i1 _value_i2 h_93 h_95 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                      exact h_110) (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                      exact h_112)) (Litex.matrixEntrywise .add _value_i4 _value_i3 _value_i1 _value_i2 h_93 h_95 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                      exact h_112) (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                      exact h_110)) (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i24 : M.Value) (_raw_i25 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) (_raw_i19 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (let _litex_matrix := (Litex.matrixEntrywise .add _value_i3 _value_i4 _value_i1 _value_i2 h_93 h_95 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                      exact h_110) (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                      exact h_112)); let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixEntrywiseInFnSet _litex_matrix)) (let _litex_matrix := (Litex.matrixEntrywise .add _value_i4 _value_i3 _value_i1 _value_i2 h_93 h_95 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                      exact h_112) (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                      exact h_110)); let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixEntrywiseInFnSet _litex_matrix)) (by rfl)
                    intro _preimage_input _preimage_domain
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i24 : M.Value) (_raw_i25 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
                    have _preimage_base : M.mem _preimage_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_93))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_95)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
                      have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
                      have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))
                    have _repack : _preimage_input = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ)))]) := (by
                      apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
                      apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
                      funext i
                      fin_cases i <;> norm_num [Litex.FiniteFunction.index])
                    exact Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (Litex.matrixEntrywise .add _value_i3 _value_i4 _value_i1 _value_i2 h_93 h_95 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                      exact h_110) (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                      exact h_112))) x = Litex.FunctionSemantics.callValue (M := M) (Litex.denote (Litex.matrixEntrywise .add _value_i4 _value_i3 _value_i1 _value_i2 h_93 h_95 (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                      exact h_112) (by
                      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_93 h_95)
                      exact h_110))) x) _repack) (_pointwise (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)) (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))
                  )
                )
            )
          exact h_114
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_addition_x5f_commutative_x2f_statement_x2e_lit
