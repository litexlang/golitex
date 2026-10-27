import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_transpose_x5f_twice_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v104 v105 v106 v107 v108
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_25 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_27 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_42 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_72 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_121 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))), (by
  let _object_h43 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)))
  have h_43 : Litex.In _value_i3 _object_h43 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27) _object_h43 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27))) h_42)
        )
    )
  let _object_w10 := (let _litex_matrix_head := (let _wd_1_0 := (Litex.transpose _value_i3 _value_i1 _value_i2 h_25 h_27 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
    exact h_42));
  let _wd_1_1 := _value_i2;
  let _wd_1_2 := _value_i1;
  (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_27 h_25 (by
    let _atomic_wd_1_0 := (Litex.transpose _value_i3 _wd_1_2 _wd_1_1 h_25 h_27 (by
      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
      exact h_42))
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_27 h_25)
    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInFnSet _litex_matrix))))));
  (let _litex_call_arg_0 := _value_i4;
  let _litex_call_arg_1 := _value_i5;
  Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.transposeInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
    exact h_72) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
    exact h_121)), True.intro⟩)))
  let _object_w11 := (let _litex_call_arg_0 := _value_i4;
  let _litex_call_arg_1 := _value_i5;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
    exact h_72) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
    exact h_121)) True.intro)
  exact (by
    let _equal_wd_1_0 := _object_w10
    let _equal_wd_1_1 := _object_w11
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_25 _Host_i2 _rep_i2 _value_i2 h_27 _Host_i3 _rep_i3 _value_i3 h_42 _Host_i4 _rep_i4 _value_i4 h_72 _Host_i5 _rep_i5 _value_i5 h_121
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
          have h_73 : Litex.In _value_i4 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i4 h_72).1
                )
            )
          have h_74 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i4 h_72).2.1
                )
            )
          have h_75 : Litex.Le _value_i4 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i4 h_72).2.2
                )
            )
          have h_76 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_72)
                )
            )
          have h_122 : Litex.In _value_i5 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i5 h_121).1
                )
            )
          have h_123 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i5 h_121).2.1
                )
            )
          have h_124 : Litex.Le _value_i5 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i5 h_121).2.2
                )
            )
          have h_125 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_121)
                )
            )
          let _object_w10 := (let _litex_matrix_head := (let _wd_1_0 := (Litex.transpose _value_i3 _value_i1 _value_i2 h_25 h_27 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
            exact h_42));
          let _wd_1_1 := _value_i2;
          let _wd_1_2 := _value_i1;
          (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_27 h_25 (by
            let _atomic_wd_1_0 := (Litex.transpose _value_i3 _wd_1_2 _wd_1_1 h_25 h_27 (by
              let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
              exact h_42))
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_27 h_25)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInFnSet _litex_matrix))))));
          (let _litex_call_arg_0 := _value_i4;
          let _litex_call_arg_1 := _value_i5;
          Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.transposeInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
            exact h_72) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
            exact h_121)), True.intro⟩)))
          let _object_w11 := (let _litex_call_arg_0 := _value_i4;
          let _litex_call_arg_1 := _value_i5;
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i3 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_43 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
            exact h_72) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
            exact h_121)) True.intro)
          have h_1 : (by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w11
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w10;
                  let _equal_wd_1_1 := _object_w11;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show Litex.denote _equal_wd_1_0 = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i5) (Litex.denote _value_i4))) from by
                    have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i4 _value_i5))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.transposeCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i4 _value_i5)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) (fun (_litex_input : M.Value) => (fun (_raw_i94 : M.Value) (_raw_i95 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i4 _value_i5))).mpr ⟨(Litex.callArguments2_mem_cart _value_i4 _value_i5 (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
                    exact h_72) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
                    exact h_121)), True.intro⟩))
                    change Litex.denote _equal_wd_1_0 = Litex.matrixTransposeBody (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i4) (Litex.denote _value_i5)) at h
                    dsimp only [Litex.matrixConjugateTransposeBody, Litex.matrixTransposeBody] at h
                    rw [Litex.FiniteFunction.unpack_pack2] at h
                    exact h).trans (let _matrix_reduction_call := (let _litex_matrix_head := (Litex.transpose _value_i3 _value_i1 _value_i2 h_25 h_27 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
                    exact h_42));
                  (let _litex_call_arg_0 := _value_i5;
                  let _litex_call_arg_1 := _value_i4;
                  Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.transposeInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
                    exact h_121) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
                    exact h_72)), True.intro⟩)));
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i5) (Litex.denote _value_i4))) = Litex.denote _matrix_reduction_call from rfl).trans ((show Litex.denote _matrix_reduction_call = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i4) (Litex.denote _value_i5))) from by
                    have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i5 _value_i4))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.transposeCall ((_equal_wd_1_0).val.function).val.matrix (Litex.denote (Litex.callArguments2 _value_i5 _value_i4)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) (fun (_litex_input : M.Value) => (fun (_raw_i102 : M.Value) (_raw_i103 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i5 _value_i4))).mpr ⟨(Litex.callArguments2_mem_cart _value_i5 _value_i4 (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
                    exact h_121) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
                    exact h_72)), True.intro⟩))
                    change Litex.denote _matrix_reduction_call = Litex.matrixTransposeBody (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i5) (Litex.denote _value_i4)) at h
                    dsimp only [Litex.matrixConjugateTransposeBody, Litex.matrixTransposeBody] at h
                    rw [Litex.FiniteFunction.unpack_pack2] at h
                    exact h).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i4) (Litex.denote _value_i5))) = (Litex.denote _equal_wd_1_1) from rfl)))).trans (show @Eq M.Value _ _ from Eq.refl _))))
                )
            )
          exact h_1
        )
      )
  )

theorem h_5415 : ∀ {_Host_i104 : Type v104} [_rep_i104 : Litex.Representation M _Host_i104] (_value_i104 : Litex.Obj (M := M) _Host_i104) (h_5438 : Litex.In _value_i104 (Litex.N (M := M))) {_Host_i105 : Type v105} [_rep_i105 : Litex.Representation M _Host_i105] (_value_i105 : Litex.Obj (M := M) _Host_i105) (h_5440 : Litex.In _value_i105 (Litex.N (M := M))) {_Host_i106 : Type v106} [_rep_i106 : Litex.Representation M _Host_i106] (_value_i106 : Litex.Obj (M := M) _Host_i106) (h_5455 : Litex.In _value_i106 (Litex.matrixSet (Litex.R (M := M)) _value_i104 _value_i105 (Litex.isSet (Litex.R (M := M))) h_5438 h_5440)) {_Host_i107 : Type v107} [_rep_i107 : Litex.Representation M _Host_i107] (_value_i107 : Litex.Obj (M := M) _Host_i107) (h_5485 : Litex.In _value_i107 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) {_Host_i108 : Type v108} [_rep_i108 : Litex.Representation M _Host_i108] (_value_i108 : Litex.Obj (M := M) _Host_i108) (h_5534 : Litex.In _value_i108 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))), (by
  let _object_h5456 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i104 _value_i105 (Litex.isSet (Litex.R (M := M))) h_5438 h_5440)))
  have h_5456 : Litex.In _value_i106 _object_h5456 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i106 _value_i106 (Litex.matrixSet (Litex.R (M := M)) _value_i104 _value_i105 (Litex.isSet (Litex.R (M := M))) h_5438 h_5440) _object_h5456 (Litex.sameRefl _value_i106) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i104 _value_i105 (Litex.isSet (Litex.R (M := M))) h_5438 h_5440))) h_5455)
        )
    )
  let _object_w21 := (let _litex_matrix_head := (let _wd_1_0 := (Litex.transpose _value_i106 _value_i104 _value_i105 h_5438 h_5440 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i104 _value_i105 (Litex.isSet (Litex.C (M := M))) h_5438 h_5440)
    exact (show Litex.In _value_i106 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i115 : M.Value) (_raw_i116 : M.Value), M.mem _raw_i115 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → M.mem _raw_i116 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → ((fun (_raw_i115 : M.Value) (_raw_i116 : M.Value) => True) _raw_i115 _raw_i116) → True := (by
          intro _raw_i115 _raw_i116 h_5675 h_5680 _
          let _value_i115 := Litex.semanticObject (M := M) _raw_i115 (M.member_isSet h_5675)
          have h_5675 : Litex.In _value_i115 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_5675
          have h_5676 : Litex.In _value_i115 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i115 h_5675).1
                )
            )
          have h_5677 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i115 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i115 h_5675).2.1
                )
            )
          have h_5678 : Litex.Le _value_i115 _value_i104 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i115 h_5675).2.2
                )
            )
          have h_5679 : Litex.In _value_i115 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i115 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5675)
                )
            )
          let _value_i116 := Litex.semanticObject (M := M) _raw_i116 (M.member_isSet h_5680)
          have h_5680 : Litex.In _value_i116 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_5680
          have h_5681 : Litex.In _value_i116 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i116 h_5680).1
                )
            )
          have h_5682 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i116 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i116 h_5680).2.1
                )
            )
          have h_5683 : Litex.Le _value_i116 _value_i105 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i116 h_5680).2.2
                )
            )
          have h_5684 : Litex.In _value_i116 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i116 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5680)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i115 : M.Value) (_raw_i116 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i106 _value_i106 _object_h5456 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5456
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_5456))))));
  let _wd_1_1 := _value_i105;
  let _wd_1_2 := _value_i104;
  (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_5440 h_5438 (by
    let _atomic_wd_1_0 := (Litex.transpose _value_i106 _wd_1_2 _wd_1_1 h_5438 h_5440 (by
      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_5438 h_5440)
      exact (show Litex.In _value_i106 _atomic_wd_2_1 from (Litex.functionRealToComplex (by
        let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i121 : M.Value) (_raw_i122 : M.Value), M.mem _raw_i121 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → M.mem _raw_i122 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → ((fun (_raw_i121 : M.Value) (_raw_i122 : M.Value) => True) _raw_i121 _raw_i122) → True := (by
            intro _raw_i121 _raw_i122 h_5846 h_5851 _
            let _value_i121 := Litex.semanticObject (M := M) _raw_i121 (M.member_isSet h_5846)
            have h_5846 : Litex.In _value_i121 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_5846
            have h_5847 : Litex.In _value_i121 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i121 h_5846).1
                  )
              )
            have h_5848 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i121 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i121 h_5846).2.1
                  )
              )
            have h_5849 : Litex.Le _value_i121 _wd_1_2 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i121 h_5846).2.2
                  )
              )
            have h_5850 : Litex.In _value_i121 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i121 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5846)
                  )
              )
            let _value_i122 := Litex.semanticObject (M := M) _raw_i122 (M.member_isSet h_5851)
            have h_5851 : Litex.In _value_i122 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_5851
            have h_5852 : Litex.In _value_i122 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i122 h_5851).1
                  )
              )
            have h_5853 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i122 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i122 h_5851).2.1
                  )
              )
            have h_5854 : Litex.Le _value_i122 _wd_1_1 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i122 h_5851).2.2
                  )
              )
            have h_5855 : Litex.In _value_i122 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i122 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5851)
                  )
              )
            exact True.intro);
          Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i121 : M.Value) (_raw_i122 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
        exact (Litex.inOfSame _value_i106 _value_i106 _object_h5456 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
          let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5456
          let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
          exact (show Litex.Same _left _right from rfl)) h_5456))))))
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_5440 h_5438)
    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i127 : M.Value) (_raw_i128 : M.Value), M.mem _raw_i127 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → M.mem _raw_i128 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → ((fun (_raw_i127 : M.Value) (_raw_i128 : M.Value) => True) _raw_i127 _raw_i128) → True := (by
          intro _raw_i127 _raw_i128 h_5922 h_5927 _
          let _value_i127 := Litex.semanticObject (M := M) _raw_i127 (M.member_isSet h_5922)
          have h_5922 : Litex.In _value_i127 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_5922
          have h_5923 : Litex.In _value_i127 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i127 h_5922).1
                )
            )
          have h_5924 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i127 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i127 h_5922).2.1
                )
            )
          have h_5925 : Litex.Le _value_i127 _wd_1_2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i127 h_5922).2.2
                )
            )
          have h_5926 : Litex.In _value_i127 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i127 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5922)
                )
            )
          let _value_i128 := Litex.semanticObject (M := M) _raw_i128 (M.member_isSet h_5927)
          have h_5927 : Litex.In _value_i128 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_5927
          have h_5928 : Litex.In _value_i128 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i128 h_5927).1
                )
            )
          have h_5929 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i128 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i128 h_5927).2.1
                )
            )
          have h_5930 : Litex.Le _value_i128 _wd_1_1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i128 h_5927).2.2
                )
            )
          have h_5931 : Litex.In _value_i128 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i128 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5927)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i127 : M.Value) (_raw_i128 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i106 _value_i106 _object_h5456 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5456
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_5456)))))))));
  (let _litex_call_arg_0 := _value_i107;
  let _litex_call_arg_1 := _value_i108;
  Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.transposeInRealFnSet _litex_matrix_head (by
    let _atomic_wd_1_0 := (Litex.transpose _value_i106 _value_i104 _value_i105 h_5438 h_5440 (by
      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i104 _value_i105 (Litex.isSet (Litex.C (M := M))) h_5438 h_5440)
      exact (show Litex.In _value_i106 _atomic_wd_2_1 from (Litex.functionRealToComplex (by
        let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i137 : M.Value) (_raw_i138 : M.Value), M.mem _raw_i137 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → M.mem _raw_i138 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → ((fun (_raw_i137 : M.Value) (_raw_i138 : M.Value) => True) _raw_i137 _raw_i138) → True := (by
            intro _raw_i137 _raw_i138 h_6081 h_6086 _
            let _value_i137 := Litex.semanticObject (M := M) _raw_i137 (M.member_isSet h_6081)
            have h_6081 : Litex.In _value_i137 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_6081
            have h_6082 : Litex.In _value_i137 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i137 h_6081).1
                  )
              )
            have h_6083 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i137 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i137 h_6081).2.1
                  )
              )
            have h_6084 : Litex.Le _value_i137 _value_i104 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i137 h_6081).2.2
                  )
              )
            have h_6085 : Litex.In _value_i137 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i137 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6081)
                  )
              )
            let _value_i138 := Litex.semanticObject (M := M) _raw_i138 (M.member_isSet h_6086)
            have h_6086 : Litex.In _value_i138 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_6086
            have h_6087 : Litex.In _value_i138 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i138 h_6086).1
                  )
              )
            have h_6088 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i138 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i138 h_6086).2.1
                  )
              )
            have h_6089 : Litex.Le _value_i138 _value_i105 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i138 h_6086).2.2
                  )
              )
            have h_6090 : Litex.In _value_i138 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i138 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6086)
                  )
              )
            exact True.intro);
          Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i137 : M.Value) (_raw_i138 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
        exact (Litex.inOfSame _value_i106 _value_i106 _object_h5456 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
          let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5456
          let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
          exact (show Litex.Same _left _right from rfl)) h_5456))))))
    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i131 : M.Value) (_raw_i132 : M.Value), M.mem _raw_i131 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → M.mem _raw_i132 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → ((fun (_raw_i131 : M.Value) (_raw_i132 : M.Value) => True) _raw_i131 _raw_i132) → True := (by
        intro _raw_i131 _raw_i132 h_6103 h_6108 _
        let _value_i131 := Litex.semanticObject (M := M) _raw_i131 (M.member_isSet h_6103)
        have h_6103 : Litex.In _value_i131 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_6103
        have h_6104 : Litex.In _value_i131 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i131 h_6103).1
              )
          )
        have h_6105 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i131 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i131 h_6103).2.1
              )
          )
        have h_6106 : Litex.Le _value_i131 _value_i105 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i131 h_6103).2.2
              )
          )
        have h_6107 : Litex.In _value_i131 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i131 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6103)
              )
          )
        let _value_i132 := Litex.semanticObject (M := M) _raw_i132 (M.member_isSet h_6108)
        have h_6108 : Litex.In _value_i132 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_6108
        have h_6109 : Litex.In _value_i132 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i132 h_6108).1
              )
          )
        have h_6110 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i132 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i132 h_6108).2.1
              )
          )
        have h_6111 : Litex.Le _value_i132 _value_i104 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i132 h_6108).2.2
              )
          )
        have h_6112 : Litex.In _value_i132 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i132 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6108)
              )
          )
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i131 : M.Value) (_raw_i132 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i139 : M.Value) (_raw_i140 : M.Value), M.mem _raw_i139 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → M.mem _raw_i140 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → ((fun (_raw_i139 : M.Value) (_raw_i140 : M.Value) => True) _raw_i139 _raw_i140) → True := (by
          intro _raw_i139 _raw_i140 h_6154 h_6159 _
          let _value_i139 := Litex.semanticObject (M := M) _raw_i139 (M.member_isSet h_6154)
          have h_6154 : Litex.In _value_i139 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_6154
          have h_6155 : Litex.In _value_i139 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i139 h_6154).1
                )
            )
          have h_6156 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i139 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i139 h_6154).2.1
                )
            )
          have h_6157 : Litex.Le _value_i139 _value_i104 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i139 h_6154).2.2
                )
            )
          have h_6158 : Litex.In _value_i139 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i139 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6154)
                )
            )
          let _value_i140 := Litex.semanticObject (M := M) _raw_i140 (M.member_isSet h_6159)
          have h_6159 : Litex.In _value_i140 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_6159
          have h_6160 : Litex.In _value_i140 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i140 h_6159).1
                )
            )
          have h_6161 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i140 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i140 h_6159).2.1
                )
            )
          have h_6162 : Litex.Le _value_i140 _value_i105 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i140 h_6159).2.2
                )
            )
          have h_6163 : Litex.In _value_i140 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i140 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6159)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i139 : M.Value) (_raw_i140 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i106 _value_i106 _object_h5456 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5456
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_5456))))))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))
    exact h_5485) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))
    exact h_5534)), True.intro⟩)))
  let _object_w22 := (let _litex_call_arg_0 := _value_i107;
  let _litex_call_arg_1 := _value_i108;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i109 : M.Value) (_raw_i110 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i106 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_5456 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))
    exact h_5485) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))
    exact h_5534)) True.intro)
  exact (by
    let _equal_wd_1_0 := _object_w21
    let _equal_wd_1_1 := _object_w22
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i104 _rep_i104 _value_i104 h_5438 _Host_i105 _rep_i105 _value_i105 h_5440 _Host_i106 _rep_i106 _value_i106 h_5455 _Host_i107 _rep_i107 _value_i107 h_5485 _Host_i108 _rep_i108 _value_i108 h_5534
          have h_5439 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i104 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i104 h_5438)
                )
            )
          have h_5441 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i105 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i105 h_5440)
                )
            )
          let _object_h5456 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i104 _value_i105 (Litex.isSet (Litex.R (M := M))) h_5438 h_5440)))
          have h_5456 : Litex.In _value_i106 _object_h5456 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i106 _value_i106 (Litex.matrixSet (Litex.R (M := M)) _value_i104 _value_i105 (Litex.isSet (Litex.R (M := M))) h_5438 h_5440) _object_h5456 (Litex.sameRefl _value_i106) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i104 _value_i105 (Litex.isSet (Litex.R (M := M))) h_5438 h_5440))) h_5455)
                )
            )
          have h_5486 : Litex.In _value_i107 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i107 h_5485).1
                )
            )
          have h_5487 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i107 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i107 h_5485).2.1
                )
            )
          have h_5488 : Litex.Le _value_i107 _value_i104 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i107 h_5485).2.2
                )
            )
          have h_5489 : Litex.In _value_i107 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i107 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5485)
                )
            )
          have h_5535 : Litex.In _value_i108 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i108 h_5534).1
                )
            )
          have h_5536 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i108 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i108 h_5534).2.1
                )
            )
          have h_5537 : Litex.Le _value_i108 _value_i105 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i108 h_5534).2.2
                )
            )
          have h_5538 : Litex.In _value_i108 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i108 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5534)
                )
            )
          let _object_w21 := (let _litex_matrix_head := (let _wd_1_0 := (Litex.transpose _value_i106 _value_i104 _value_i105 h_5438 h_5440 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i104 _value_i105 (Litex.isSet (Litex.C (M := M))) h_5438 h_5440)
            exact (show Litex.In _value_i106 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i115 : M.Value) (_raw_i116 : M.Value), M.mem _raw_i115 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → M.mem _raw_i116 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → ((fun (_raw_i115 : M.Value) (_raw_i116 : M.Value) => True) _raw_i115 _raw_i116) → True := (by
                  intro _raw_i115 _raw_i116 h_5675 h_5680 _
                  let _value_i115 := Litex.semanticObject (M := M) _raw_i115 (M.member_isSet h_5675)
                  have h_5675 : Litex.In _value_i115 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_5675
                  have h_5676 : Litex.In _value_i115 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i115 h_5675).1
                        )
                    )
                  have h_5677 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i115 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i115 h_5675).2.1
                        )
                    )
                  have h_5678 : Litex.Le _value_i115 _value_i104 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i115 h_5675).2.2
                        )
                    )
                  have h_5679 : Litex.In _value_i115 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i115 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5675)
                        )
                    )
                  let _value_i116 := Litex.semanticObject (M := M) _raw_i116 (M.member_isSet h_5680)
                  have h_5680 : Litex.In _value_i116 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_5680
                  have h_5681 : Litex.In _value_i116 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i116 h_5680).1
                        )
                    )
                  have h_5682 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i116 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i116 h_5680).2.1
                        )
                    )
                  have h_5683 : Litex.Le _value_i116 _value_i105 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i116 h_5680).2.2
                        )
                    )
                  have h_5684 : Litex.In _value_i116 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i116 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5680)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i115 : M.Value) (_raw_i116 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i106 _value_i106 _object_h5456 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5456
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_5456))))));
          let _wd_1_1 := _value_i105;
          let _wd_1_2 := _value_i104;
          (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_5440 h_5438 (by
            let _atomic_wd_1_0 := (Litex.transpose _value_i106 _wd_1_2 _wd_1_1 h_5438 h_5440 (by
              let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_5438 h_5440)
              exact (show Litex.In _value_i106 _atomic_wd_2_1 from (Litex.functionRealToComplex (by
                let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i121 : M.Value) (_raw_i122 : M.Value), M.mem _raw_i121 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → M.mem _raw_i122 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → ((fun (_raw_i121 : M.Value) (_raw_i122 : M.Value) => True) _raw_i121 _raw_i122) → True := (by
                    intro _raw_i121 _raw_i122 h_5846 h_5851 _
                    let _value_i121 := Litex.semanticObject (M := M) _raw_i121 (M.member_isSet h_5846)
                    have h_5846 : Litex.In _value_i121 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_5846
                    have h_5847 : Litex.In _value_i121 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i121 h_5846).1
                          )
                      )
                    have h_5848 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i121 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i121 h_5846).2.1
                          )
                      )
                    have h_5849 : Litex.Le _value_i121 _wd_1_2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i121 h_5846).2.2
                          )
                      )
                    have h_5850 : Litex.In _value_i121 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i121 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5846)
                          )
                      )
                    let _value_i122 := Litex.semanticObject (M := M) _raw_i122 (M.member_isSet h_5851)
                    have h_5851 : Litex.In _value_i122 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_5851
                    have h_5852 : Litex.In _value_i122 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i122 h_5851).1
                          )
                      )
                    have h_5853 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i122 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i122 h_5851).2.1
                          )
                      )
                    have h_5854 : Litex.Le _value_i122 _wd_1_1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i122 h_5851).2.2
                          )
                      )
                    have h_5855 : Litex.In _value_i122 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i122 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5851)
                          )
                      )
                    exact True.intro);
                  Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
                  have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
                  have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i121 : M.Value) (_raw_i122 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                exact (Litex.inOfSame _value_i106 _value_i106 _object_h5456 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                  let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5456
                  let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                  exact (show Litex.Same _left _right from rfl)) h_5456))))))
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_5440 h_5438)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i127 : M.Value) (_raw_i128 : M.Value), M.mem _raw_i127 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → M.mem _raw_i128 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → ((fun (_raw_i127 : M.Value) (_raw_i128 : M.Value) => True) _raw_i127 _raw_i128) → True := (by
                  intro _raw_i127 _raw_i128 h_5922 h_5927 _
                  let _value_i127 := Litex.semanticObject (M := M) _raw_i127 (M.member_isSet h_5922)
                  have h_5922 : Litex.In _value_i127 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_5922
                  have h_5923 : Litex.In _value_i127 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i127 h_5922).1
                        )
                    )
                  have h_5924 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i127 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i127 h_5922).2.1
                        )
                    )
                  have h_5925 : Litex.Le _value_i127 _wd_1_2 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i127 h_5922).2.2
                        )
                    )
                  have h_5926 : Litex.In _value_i127 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i127 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5922)
                        )
                    )
                  let _value_i128 := Litex.semanticObject (M := M) _raw_i128 (M.member_isSet h_5927)
                  have h_5927 : Litex.In _value_i128 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_5927
                  have h_5928 : Litex.In _value_i128 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i128 h_5927).1
                        )
                    )
                  have h_5929 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i128 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i128 h_5927).2.1
                        )
                    )
                  have h_5930 : Litex.Le _value_i128 _wd_1_1 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i128 h_5927).2.2
                        )
                    )
                  have h_5931 : Litex.In _value_i128 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i128 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5927)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i127 : M.Value) (_raw_i128 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i106 _value_i106 _object_h5456 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5456
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_5456)))))))));
          (let _litex_call_arg_0 := _value_i107;
          let _litex_call_arg_1 := _value_i108;
          Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.transposeInRealFnSet _litex_matrix_head (by
            let _atomic_wd_1_0 := (Litex.transpose _value_i106 _value_i104 _value_i105 h_5438 h_5440 (by
              let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i104 _value_i105 (Litex.isSet (Litex.C (M := M))) h_5438 h_5440)
              exact (show Litex.In _value_i106 _atomic_wd_2_1 from (Litex.functionRealToComplex (by
                let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i137 : M.Value) (_raw_i138 : M.Value), M.mem _raw_i137 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → M.mem _raw_i138 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → ((fun (_raw_i137 : M.Value) (_raw_i138 : M.Value) => True) _raw_i137 _raw_i138) → True := (by
                    intro _raw_i137 _raw_i138 h_6081 h_6086 _
                    let _value_i137 := Litex.semanticObject (M := M) _raw_i137 (M.member_isSet h_6081)
                    have h_6081 : Litex.In _value_i137 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_6081
                    have h_6082 : Litex.In _value_i137 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i137 h_6081).1
                          )
                      )
                    have h_6083 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i137 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i137 h_6081).2.1
                          )
                      )
                    have h_6084 : Litex.Le _value_i137 _value_i104 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i137 h_6081).2.2
                          )
                      )
                    have h_6085 : Litex.In _value_i137 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i137 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6081)
                          )
                      )
                    let _value_i138 := Litex.semanticObject (M := M) _raw_i138 (M.member_isSet h_6086)
                    have h_6086 : Litex.In _value_i138 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_6086
                    have h_6087 : Litex.In _value_i138 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i138 h_6086).1
                          )
                      )
                    have h_6088 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i138 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i138 h_6086).2.1
                          )
                      )
                    have h_6089 : Litex.Le _value_i138 _value_i105 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i138 h_6086).2.2
                          )
                      )
                    have h_6090 : Litex.In _value_i138 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i138 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6086)
                          )
                      )
                    exact True.intro);
                  Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
                  have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
                  have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i137 : M.Value) (_raw_i138 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                exact (Litex.inOfSame _value_i106 _value_i106 _object_h5456 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                  let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5456
                  let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                  exact (show Litex.Same _left _right from rfl)) h_5456))))))
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i131 : M.Value) (_raw_i132 : M.Value), M.mem _raw_i131 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → M.mem _raw_i132 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → ((fun (_raw_i131 : M.Value) (_raw_i132 : M.Value) => True) _raw_i131 _raw_i132) → True := (by
                intro _raw_i131 _raw_i132 h_6103 h_6108 _
                let _value_i131 := Litex.semanticObject (M := M) _raw_i131 (M.member_isSet h_6103)
                have h_6103 : Litex.In _value_i131 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_6103
                have h_6104 : Litex.In _value_i131 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i131 h_6103).1
                      )
                  )
                have h_6105 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i131 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i131 h_6103).2.1
                      )
                  )
                have h_6106 : Litex.Le _value_i131 _value_i105 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i131 h_6103).2.2
                      )
                  )
                have h_6107 : Litex.In _value_i131 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i131 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6103)
                      )
                  )
                let _value_i132 := Litex.semanticObject (M := M) _raw_i132 (M.member_isSet h_6108)
                have h_6108 : Litex.In _value_i132 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_6108
                have h_6109 : Litex.In _value_i132 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i132 h_6108).1
                      )
                  )
                have h_6110 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i132 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i132 h_6108).2.1
                      )
                  )
                have h_6111 : Litex.Le _value_i132 _value_i104 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i132 h_6108).2.2
                      )
                  )
                have h_6112 : Litex.In _value_i132 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i132 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6108)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))] (by
              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i131 : M.Value) (_raw_i132 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i139 : M.Value) (_raw_i140 : M.Value), M.mem _raw_i139 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → M.mem _raw_i140 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → ((fun (_raw_i139 : M.Value) (_raw_i140 : M.Value) => True) _raw_i139 _raw_i140) → True := (by
                  intro _raw_i139 _raw_i140 h_6154 h_6159 _
                  let _value_i139 := Litex.semanticObject (M := M) _raw_i139 (M.member_isSet h_6154)
                  have h_6154 : Litex.In _value_i139 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_6154
                  have h_6155 : Litex.In _value_i139 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i139 h_6154).1
                        )
                    )
                  have h_6156 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i139 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i139 h_6154).2.1
                        )
                    )
                  have h_6157 : Litex.Le _value_i139 _value_i104 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i139 h_6154).2.2
                        )
                    )
                  have h_6158 : Litex.In _value_i139 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i139 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6154)
                        )
                    )
                  let _value_i140 := Litex.semanticObject (M := M) _raw_i140 (M.member_isSet h_6159)
                  have h_6159 : Litex.In _value_i140 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_6159
                  have h_6160 : Litex.In _value_i140 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i140 h_6159).1
                        )
                    )
                  have h_6161 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i140 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i140 h_6159).2.1
                        )
                    )
                  have h_6162 : Litex.Le _value_i140 _value_i105 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i140 h_6159).2.2
                        )
                    )
                  have h_6163 : Litex.In _value_i140 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i140 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6159)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i139 : M.Value) (_raw_i140 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i106 _value_i106 _object_h5456 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5456
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_5456))))))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))
            exact h_5485) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))
            exact h_5534)), True.intro⟩)))
          let _object_w22 := (let _litex_call_arg_0 := _value_i107;
          let _litex_call_arg_1 := _value_i108;
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i109 : M.Value) (_raw_i110 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i106 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_5456 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))
            exact h_5485) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))
            exact h_5534)) True.intro)
          have h_5414 : (by
            let _equal_wd_1_0 := _object_w21
            let _equal_wd_1_1 := _object_w22
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w21;
                  let _equal_wd_1_1 := _object_w22;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show Litex.denote _equal_wd_1_0 = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i108) (Litex.denote _value_i107))) from by
                    have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i107 _value_i108))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.transposeCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i107 _value_i108)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) (fun (_litex_input : M.Value) => (fun (_raw_i157 : M.Value) (_raw_i158 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i107 _value_i108))).mpr ⟨(Litex.callArguments2_mem_cart _value_i107 _value_i108 (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))
                    exact h_5485) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))
                    exact h_5534)), True.intro⟩))
                    change Litex.denote _equal_wd_1_0 = Litex.matrixTransposeBody (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i107) (Litex.denote _value_i108)) at h
                    dsimp only [Litex.matrixConjugateTransposeBody, Litex.matrixTransposeBody] at h
                    rw [Litex.FiniteFunction.unpack_pack2] at h
                    exact h).trans (let _matrix_reduction_call := (let _litex_matrix_head := (Litex.transpose _value_i106 _value_i104 _value_i105 h_5438 h_5440 (by
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i104 _value_i105 (Litex.isSet (Litex.C (M := M))) h_5438 h_5440)
                    exact (show Litex.In _value_i106 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i163 : M.Value) (_raw_i164 : M.Value), M.mem _raw_i163 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → M.mem _raw_i164 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → ((fun (_raw_i163 : M.Value) (_raw_i164 : M.Value) => True) _raw_i163 _raw_i164) → True := (by
                          intro _raw_i163 _raw_i164 h_6822 h_6827 _
                          let _value_i163 := Litex.semanticObject (M := M) _raw_i163 (M.member_isSet h_6822)
                          have h_6822 : Litex.In _value_i163 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_6822
                          have h_6823 : Litex.In _value_i163 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i163 h_6822).1
                                )
                            )
                          have h_6824 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i163 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i163 h_6822).2.1
                                )
                            )
                          have h_6825 : Litex.Le _value_i163 _value_i104 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i163 h_6822).2.2
                                )
                            )
                          have h_6826 : Litex.In _value_i163 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i163 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6822)
                                )
                            )
                          let _value_i164 := Litex.semanticObject (M := M) _raw_i164 (M.member_isSet h_6827)
                          have h_6827 : Litex.In _value_i164 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_6827
                          have h_6828 : Litex.In _value_i164 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i164 h_6827).1
                                )
                            )
                          have h_6829 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i164 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i164 h_6827).2.1
                                )
                            )
                          have h_6830 : Litex.Le _value_i164 _value_i105 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i164 h_6827).2.2
                                )
                            )
                          have h_6831 : Litex.In _value_i164 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i164 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6827)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i163 : M.Value) (_raw_i164 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i106 _value_i106 _object_h5456 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5456
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_5456))))));
                  (let _litex_call_arg_0 := _value_i108;
                  let _litex_call_arg_1 := _value_i107;
                  Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.transposeInRealFnSet _litex_matrix_head (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i165 : M.Value) (_raw_i166 : M.Value), M.mem _raw_i165 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))) → M.mem _raw_i166 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))) → ((fun (_raw_i165 : M.Value) (_raw_i166 : M.Value) => True) _raw_i165 _raw_i166) → True := (by
                        intro _raw_i165 _raw_i166 h_6845 h_6850 _
                        let _value_i165 := Litex.semanticObject (M := M) _raw_i165 (M.member_isSet h_6845)
                        have h_6845 : Litex.In _value_i165 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) := h_6845
                        have h_6846 : Litex.In _value_i165 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i165 h_6845).1
                              )
                          )
                        have h_6847 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i165 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i165 h_6845).2.1
                              )
                          )
                        have h_6848 : Litex.Le _value_i165 _value_i104 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i165 h_6845).2.2
                              )
                          )
                        have h_6849 : Litex.In _value_i165 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)) _value_i165 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6845)
                              )
                          )
                        let _value_i166 := Litex.semanticObject (M := M) _raw_i166 (M.member_isSet h_6850)
                        have h_6850 : Litex.In _value_i166 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) := h_6850
                        have h_6851 : Litex.In _value_i166 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i166 h_6850).1
                              )
                          )
                        have h_6852 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i166 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i166 h_6850).2.1
                              )
                          )
                        have h_6853 : Litex.Le _value_i166 _value_i105 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i166 h_6850).2.2
                              )
                          )
                        have h_6854 : Litex.In _value_i166 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)) _value_i166 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6850)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i165 : M.Value) (_raw_i166 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                    exact (Litex.inOfSame _value_i106 _value_i106 _object_h5456 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5456
                      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) h_5456))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))
                    exact h_5534) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))
                    exact h_5485)), True.intro⟩)));
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i108) (Litex.denote _value_i107))) = Litex.denote _matrix_reduction_call from rfl).trans ((show Litex.denote _matrix_reduction_call = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i107) (Litex.denote _value_i108))) from by
                    have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i108 _value_i107))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.transposeCall ((_equal_wd_1_0).val.function).val.matrix (Litex.denote (Litex.callArguments2 _value_i108 _value_i107)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) (fun (_litex_input : M.Value) => (fun (_raw_i171 : M.Value) (_raw_i172 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i108 _value_i107))).mpr ⟨(Litex.callArguments2_mem_cart _value_i108 _value_i107 (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i105 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i105 h_5440))
                    exact h_5534) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i104 h_5438))
                    exact h_5485)), True.intro⟩))
                    change Litex.denote _matrix_reduction_call = Litex.matrixTransposeBody (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i108) (Litex.denote _value_i107)) at h
                    dsimp only [Litex.matrixConjugateTransposeBody, Litex.matrixTransposeBody] at h
                    rw [Litex.FiniteFunction.unpack_pack2] at h
                    exact h).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (((_equal_wd_1_0).val.function).val.matrix).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i107) (Litex.denote _value_i108))) = (Litex.denote _equal_wd_1_1) from rfl)))).trans (show @Eq M.Value _ _ from Eq.refl _))))
                )
            )
          exact h_5414
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_transpose_x5f_twice_x2f_statement_x2e_lit
