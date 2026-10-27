import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_scale_x5f_coordinates_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v43 v44 v45 v46 v47 v48
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_37 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_39 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_41 : Litex.In _value_i3 (Litex.C (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_55 : Litex.In _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_37 h_39)) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_90 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_144 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39))), (by
  let _object_h56 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_37 h_39)))
  have h_56 : Litex.In _value_i4 _object_h56 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_37 h_39) _object_h56 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_37 h_39))) h_55)
        )
    )
  let _object_w11 := (let _litex_matrix_head := (Litex.matrixScale _value_i3 _value_i4 _value_i1 _value_i2 h_41 h_37 h_39 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_37 h_39)
    exact h_55));
  (let _litex_call_arg_0 := _value_i5;
  let _litex_call_arg_1 := _value_i6;
  Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixScaleInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37))
    exact h_90) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39))
    exact h_144)), True.intro⟩)))
  let _object_w12 := (let _wd_1_0 := _value_i3;
  let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
  let _litex_call_arg_1 := _value_i6;
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39)))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37)))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39)))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_56 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37))
    exact h_90) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39))
    exact h_144)) True.intro);
  (Litex.mul _wd_1_0 _wd_1_1 h_41 (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
  exact (by
    let _equal_wd_1_0 := _object_w11
    let _equal_wd_1_1 := _object_w12
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_37 _Host_i2 _rep_i2 _value_i2 h_39 _Host_i3 _rep_i3 _value_i3 h_41 _Host_i4 _rep_i4 _value_i4 h_55 _Host_i5 _rep_i5 _value_i5 h_90 _Host_i6 _rep_i6 _value_i6 h_144
          have h_38 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_37)
                )
            )
          have h_40 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_39)
                )
            )
          let _object_h56 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_37 h_39)))
          have h_56 : Litex.In _value_i4 _object_h56 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_37 h_39) _object_h56 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_37 h_39))) h_55)
                )
            )
          have h_91 : Litex.In _value_i5 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37)) _value_i5 h_90).1
                )
            )
          have h_92 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37)) _value_i5 h_90).2.1
                )
            )
          have h_93 : Litex.Le _value_i5 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37)) _value_i5 h_90).2.2
                )
            )
          have h_94 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_90)
                )
            )
          have h_145 : Litex.In _value_i6 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39)) _value_i6 h_144).1
                )
            )
          have h_146 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39)) _value_i6 h_144).2.1
                )
            )
          have h_147 : Litex.Le _value_i6 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39)) _value_i6 h_144).2.2
                )
            )
          have h_148 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_144)
                )
            )
          let _object_w11 := (let _litex_matrix_head := (Litex.matrixScale _value_i3 _value_i4 _value_i1 _value_i2 h_41 h_37 h_39 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_37 h_39)
            exact h_55));
          (let _litex_call_arg_0 := _value_i5;
          let _litex_call_arg_1 := _value_i6;
          Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixScaleInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37))
            exact h_90) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39))
            exact h_144)), True.intro⟩)))
          let _object_w12 := (let _wd_1_0 := _value_i3;
          let _wd_1_1 := (let _litex_call_arg_0 := _value_i5;
          let _litex_call_arg_1 := _value_i6;
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39)))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37)))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39)))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_56 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37))
            exact h_90) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39))
            exact h_144)) True.intro);
          (Litex.mul _wd_1_0 _wd_1_1 h_41 (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w11;
                  let _equal_wd_1_1 := _object_w12;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show Litex.denote _equal_wd_1_0 = (M.mulValue (Litex.denote ((_equal_wd_1_0).val.function).val.scalar) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i5) (Litex.denote _value_i6)))) from by
                    have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i5 _value_i6))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.matrixScaleCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i5 _value_i6)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) (fun (_litex_input : M.Value) => (fun (_raw_i41 : M.Value) (_raw_i42 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i5 _value_i6))).mpr ⟨(Litex.callArguments2_mem_cart _value_i5 _value_i6 (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_37))
                    exact h_90) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_39))
                    exact h_144)), True.intro⟩))
                    change Litex.denote _equal_wd_1_0 = Litex.matrixScaleBody (Litex.denote ((_equal_wd_1_0).val.function).val.scalar) (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i5) (Litex.denote _value_i6)) at h
                    dsimp only [Litex.matrixScaleBody] at h
                    rw [Litex.FiniteFunction.unpack_pack2] at h
                    exact h).trans (show (M.mulValue (Litex.denote ((_equal_wd_1_0).val.function).val.scalar) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote _value_i5) (Litex.denote _value_i6)))) = (Litex.denote _equal_wd_1_1) from rfl)).trans (show @Eq M.Value _ _ from Eq.refl _))))
                )
            )
          exact h_1
        )
      )
  )

theorem h_5367 : ∀ {_Host_i43 : Type v43} [_rep_i43 : Litex.Representation M _Host_i43] (_value_i43 : Litex.Obj (M := M) _Host_i43) (h_5402 : Litex.In _value_i43 (Litex.N (M := M))) {_Host_i44 : Type v44} [_rep_i44 : Litex.Representation M _Host_i44] (_value_i44 : Litex.Obj (M := M) _Host_i44) (h_5404 : Litex.In _value_i44 (Litex.N (M := M))) {_Host_i45 : Type v45} [_rep_i45 : Litex.Representation M _Host_i45] (_value_i45 : Litex.Obj (M := M) _Host_i45) (h_5406 : Litex.In _value_i45 (Litex.R (M := M))) {_Host_i46 : Type v46} [_rep_i46 : Litex.Representation M _Host_i46] (_value_i46 : Litex.Obj (M := M) _Host_i46) (h_5420 : Litex.In _value_i46 (Litex.matrixSet (Litex.R (M := M)) _value_i43 _value_i44 (Litex.isSet (Litex.R (M := M))) h_5402 h_5404)) {_Host_i47 : Type v47} [_rep_i47 : Litex.Representation M _Host_i47] (_value_i47 : Litex.Obj (M := M) _Host_i47) (h_5455 : Litex.In _value_i47 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))) {_Host_i48 : Type v48} [_rep_i48 : Litex.Representation M _Host_i48] (_value_i48 : Litex.Obj (M := M) _Host_i48) (h_5509 : Litex.In _value_i48 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404))), (by
  let _object_h5421 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i43 _value_i44 (Litex.isSet (Litex.R (M := M))) h_5402 h_5404)))
  have h_5421 : Litex.In _value_i46 _object_h5421 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i46 _value_i46 (Litex.matrixSet (Litex.R (M := M)) _value_i43 _value_i44 (Litex.isSet (Litex.R (M := M))) h_5402 h_5404) _object_h5421 (Litex.sameRefl _value_i46) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i43 _value_i44 (Litex.isSet (Litex.R (M := M))) h_5402 h_5404))) h_5420)
        )
    )
  let _object_w23 := (let _litex_matrix_head := (Litex.matrixScale _value_i45 _value_i46 _value_i43 _value_i44 (M.real_subset_complex _ h_5406) h_5402 h_5404 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i43 _value_i44 (Litex.isSet (Litex.C (M := M))) h_5402 h_5404)
    exact (show Litex.In _value_i46 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i55 : M.Value) (_raw_i56 : M.Value), M.mem _raw_i55 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))) → M.mem _raw_i56 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404))) → ((fun (_raw_i55 : M.Value) (_raw_i56 : M.Value) => True) _raw_i55 _raw_i56) → True := (by
          intro _raw_i55 _raw_i56 h_5700 h_5705 _
          let _value_i55 := Litex.semanticObject (M := M) _raw_i55 (M.member_isSet h_5700)
          have h_5700 : Litex.In _value_i55 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) := h_5700
          have h_5701 : Litex.In _value_i55 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i55 h_5700).1
                )
            )
          have h_5702 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i55 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i55 h_5700).2.1
                )
            )
          have h_5703 : Litex.Le _value_i55 _value_i43 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i55 h_5700).2.2
                )
            )
          have h_5704 : Litex.In _value_i55 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i55 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5700)
                )
            )
          let _value_i56 := Litex.semanticObject (M := M) _raw_i56 (M.member_isSet h_5705)
          have h_5705 : Litex.In _value_i56 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) := h_5705
          have h_5706 : Litex.In _value_i56 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i56 h_5705).1
                )
            )
          have h_5707 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i56 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i56 h_5705).2.1
                )
            )
          have h_5708 : Litex.Le _value_i56 _value_i44 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i56 h_5705).2.2
                )
            )
          have h_5709 : Litex.In _value_i56 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i56 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5705)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i55 : M.Value) (_raw_i56 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i46 _value_i46 _object_h5421 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5421
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_5421))))));
  (let _litex_call_arg_0 := _value_i47;
  let _litex_call_arg_1 := _value_i48;
  Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixScaleInRealFnSet _litex_matrix_head (by
    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i57 : M.Value) (_raw_i58 : M.Value), M.mem _raw_i57 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))) → M.mem _raw_i58 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404))) → ((fun (_raw_i57 : M.Value) (_raw_i58 : M.Value) => True) _raw_i57 _raw_i58) → True := (by
        intro _raw_i57 _raw_i58 h_5725 h_5730 _
        let _value_i57 := Litex.semanticObject (M := M) _raw_i57 (M.member_isSet h_5725)
        have h_5725 : Litex.In _value_i57 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) := h_5725
        have h_5726 : Litex.In _value_i57 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i57 h_5725).1
              )
          )
        have h_5727 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i57 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i57 h_5725).2.1
              )
          )
        have h_5728 : Litex.Le _value_i57 _value_i43 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i57 h_5725).2.2
              )
          )
        have h_5729 : Litex.In _value_i57 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i57 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5725)
              )
          )
        let _value_i58 := Litex.semanticObject (M := M) _raw_i58 (M.member_isSet h_5730)
        have h_5730 : Litex.In _value_i58 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) := h_5730
        have h_5731 : Litex.In _value_i58 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i58 h_5730).1
              )
          )
        have h_5732 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i58 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i58 h_5730).2.1
              )
          )
        have h_5733 : Litex.Le _value_i58 _value_i44 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i58 h_5730).2.2
              )
          )
        have h_5734 : Litex.In _value_i58 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i58 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5730)
              )
          )
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)))
      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i57 : M.Value) (_raw_i58 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
    exact (Litex.inOfSame _value_i46 _value_i46 _object_h5421 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5421
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_5421)) h_5406) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))
    exact h_5455) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404))
    exact h_5509)), True.intro⟩)))
  exact (by
    let _atomic_wd_1_0 := _object_w23
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i43 _rep_i43 _value_i43 h_5402 _Host_i44 _rep_i44 _value_i44 h_5404 _Host_i45 _rep_i45 _value_i45 h_5406 _Host_i46 _rep_i46 _value_i46 h_5420 _Host_i47 _rep_i47 _value_i47 h_5455 _Host_i48 _rep_i48 _value_i48 h_5509
          have h_5403 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i43 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i43 h_5402)
                )
            )
          have h_5405 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i44 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i44 h_5404)
                )
            )
          let _object_h5421 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i43 _value_i44 (Litex.isSet (Litex.R (M := M))) h_5402 h_5404)))
          have h_5421 : Litex.In _value_i46 _object_h5421 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i46 _value_i46 (Litex.matrixSet (Litex.R (M := M)) _value_i43 _value_i44 (Litex.isSet (Litex.R (M := M))) h_5402 h_5404) _object_h5421 (Litex.sameRefl _value_i46) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i43 _value_i44 (Litex.isSet (Litex.R (M := M))) h_5402 h_5404))) h_5420)
                )
            )
          have h_5456 : Litex.In _value_i47 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i47 h_5455).1
                )
            )
          have h_5457 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i47 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i47 h_5455).2.1
                )
            )
          have h_5458 : Litex.Le _value_i47 _value_i43 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i47 h_5455).2.2
                )
            )
          have h_5459 : Litex.In _value_i47 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i47 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5455)
                )
            )
          have h_5510 : Litex.In _value_i48 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i48 h_5509).1
                )
            )
          have h_5511 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i48 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i48 h_5509).2.1
                )
            )
          have h_5512 : Litex.Le _value_i48 _value_i44 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i48 h_5509).2.2
                )
            )
          have h_5513 : Litex.In _value_i48 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i48 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5509)
                )
            )
          let _object_w23 := (let _litex_matrix_head := (Litex.matrixScale _value_i45 _value_i46 _value_i43 _value_i44 (M.real_subset_complex _ h_5406) h_5402 h_5404 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i43 _value_i44 (Litex.isSet (Litex.C (M := M))) h_5402 h_5404)
            exact (show Litex.In _value_i46 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i55 : M.Value) (_raw_i56 : M.Value), M.mem _raw_i55 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))) → M.mem _raw_i56 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404))) → ((fun (_raw_i55 : M.Value) (_raw_i56 : M.Value) => True) _raw_i55 _raw_i56) → True := (by
                  intro _raw_i55 _raw_i56 h_5700 h_5705 _
                  let _value_i55 := Litex.semanticObject (M := M) _raw_i55 (M.member_isSet h_5700)
                  have h_5700 : Litex.In _value_i55 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) := h_5700
                  have h_5701 : Litex.In _value_i55 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i55 h_5700).1
                        )
                    )
                  have h_5702 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i55 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i55 h_5700).2.1
                        )
                    )
                  have h_5703 : Litex.Le _value_i55 _value_i43 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i55 h_5700).2.2
                        )
                    )
                  have h_5704 : Litex.In _value_i55 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i55 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5700)
                        )
                    )
                  let _value_i56 := Litex.semanticObject (M := M) _raw_i56 (M.member_isSet h_5705)
                  have h_5705 : Litex.In _value_i56 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) := h_5705
                  have h_5706 : Litex.In _value_i56 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i56 h_5705).1
                        )
                    )
                  have h_5707 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i56 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i56 h_5705).2.1
                        )
                    )
                  have h_5708 : Litex.Le _value_i56 _value_i44 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i56 h_5705).2.2
                        )
                    )
                  have h_5709 : Litex.In _value_i56 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i56 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5705)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i55 : M.Value) (_raw_i56 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i46 _value_i46 _object_h5421 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5421
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_5421))))));
          (let _litex_call_arg_0 := _value_i47;
          let _litex_call_arg_1 := _value_i48;
          Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixScaleInRealFnSet _litex_matrix_head (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i57 : M.Value) (_raw_i58 : M.Value), M.mem _raw_i57 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))) → M.mem _raw_i58 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404))) → ((fun (_raw_i57 : M.Value) (_raw_i58 : M.Value) => True) _raw_i57 _raw_i58) → True := (by
                intro _raw_i57 _raw_i58 h_5725 h_5730 _
                let _value_i57 := Litex.semanticObject (M := M) _raw_i57 (M.member_isSet h_5725)
                have h_5725 : Litex.In _value_i57 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) := h_5725
                have h_5726 : Litex.In _value_i57 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i57 h_5725).1
                      )
                  )
                have h_5727 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i57 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i57 h_5725).2.1
                      )
                  )
                have h_5728 : Litex.Le _value_i57 _value_i43 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i57 h_5725).2.2
                      )
                  )
                have h_5729 : Litex.In _value_i57 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i57 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5725)
                      )
                  )
                let _value_i58 := Litex.semanticObject (M := M) _raw_i58 (M.member_isSet h_5730)
                have h_5730 : Litex.In _value_i58 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) := h_5730
                have h_5731 : Litex.In _value_i58 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i58 h_5730).1
                      )
                  )
                have h_5732 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i58 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i58 h_5730).2.1
                      )
                  )
                have h_5733 : Litex.Le _value_i58 _value_i44 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i58 h_5730).2.2
                      )
                  )
                have h_5734 : Litex.In _value_i58 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i58 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5730)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))] (by
              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)))
              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i57 : M.Value) (_raw_i58 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
            exact (Litex.inOfSame _value_i46 _value_i46 _object_h5421 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5421
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_5421)) h_5406) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))
            exact h_5455) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404))
            exact h_5509)), True.intro⟩)))
          have h_5366 : (by
            let _atomic_wd_1_0 := _object_w23
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w23
                    exact (show Litex.In _atomic_wd_1_0 (Litex.R (M := M)) from (let _litex_matrix_signature := (Litex.matrixEntrywiseSignature ((_atomic_wd_1_0).val.function).val.rows ((_atomic_wd_1_0).val.function).val.cols .real); Litex.FunctionSemantics.call_mem _litex_matrix_signature.domain _litex_matrix_signature.output (Litex.denote (_atomic_wd_1_0).val.function) (Litex.denote (Litex.callArguments2 _value_i47 _value_i48)) (let _litex_matrix := (_atomic_wd_1_0).val.function; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixScaleInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i61 : M.Value) (_raw_i62 : M.Value), M.mem _raw_i61 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))) → M.mem _raw_i62 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404))) → ((fun (_raw_i61 : M.Value) (_raw_i62 : M.Value) => True) _raw_i61 _raw_i62) → True := (by
                          intro _raw_i61 _raw_i62 h_6006 h_6011 _
                          let _value_i61 := Litex.semanticObject (M := M) _raw_i61 (M.member_isSet h_6006)
                          have h_6006 : Litex.In _value_i61 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) := h_6006
                          have h_6007 : Litex.In _value_i61 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i61 h_6006).1
                                )
                            )
                          have h_6008 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i61 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i61 h_6006).2.1
                                )
                            )
                          have h_6009 : Litex.Le _value_i61 _value_i43 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i61 h_6006).2.2
                                )
                            )
                          have h_6010 : Litex.In _value_i61 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)) _value_i61 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6006)
                                )
                            )
                          let _value_i62 := Litex.semanticObject (M := M) _raw_i62 (M.member_isSet h_6011)
                          have h_6011 : Litex.In _value_i62 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) := h_6011
                          have h_6012 : Litex.In _value_i62 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i62 h_6011).1
                                )
                            )
                          have h_6013 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i62 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i62 h_6011).2.1
                                )
                            )
                          have h_6014 : Litex.Le _value_i62 _value_i44 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i62 h_6011).2.2
                                )
                            )
                          have h_6015 : Litex.In _value_i62 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)) _value_i62 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6011)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i61 : M.Value) (_raw_i62 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i46 _value_i46 _object_h5421 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h5421
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_5421)) h_5406)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))) (fun (_litex_input : M.Value) => (fun (_raw_i63 : M.Value) (_raw_i64 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i47 _value_i48))).mpr ⟨(Litex.callArguments2_mem_cart _value_i47 _value_i48 (by
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i43 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i43 h_5402))
                      exact h_5455) (by
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i44 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i44 h_5404))
                      exact h_5509)), True.intro⟩))))
                )
            )
          exact h_5366
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_scale_x5f_coordinates_x2f_statement_x2e_lit
