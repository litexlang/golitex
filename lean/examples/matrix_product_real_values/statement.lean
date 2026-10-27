import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_product_x5f_real_x5f_values_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v38 v39 v40 v41 v42
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_29 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_31 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_33 : Litex.In _value_i3 (Litex.N (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_48 : Litex.In _value_i4 (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_29 h_31)) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_67 : Litex.In _value_i5 (Litex.matrixSet (Litex.R (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.R (M := M))) h_31 h_33)) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_112 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_177 : Litex.In _value_i7 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))), (by
  let _object_h49 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_29 h_31)))
  have h_49 : Litex.In _value_i4 _object_h49 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_29 h_31) _object_h49 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_29 h_31))) h_48)
        )
    )
  let _object_h68 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.R (M := M))) h_31 h_33)))
  have h_68 : Litex.In _value_i5 _object_h68 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i5 _value_i5 (Litex.matrixSet (Litex.R (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.R (M := M))) h_31 h_33) _object_h68 (Litex.sameRefl _value_i5) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.R (M := M))) h_31 h_33))) h_67)
        )
    )
  let _object_w20 := (let _litex_matrix_head := (Litex.matrixMultiply _value_i4 _value_i5 _value_i1 _value_i2 _value_i3 h_29 h_31 h_33 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_29 h_31)
    exact (show Litex.In _value_i4 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i16 : M.Value) (_raw_i17 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))) → M.mem _raw_i17 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))) → ((fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True) _raw_i16 _raw_i17) → True := (by
          intro _raw_i16 _raw_i17 h_499 h_504 _
          let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_499)
          have h_499 : Litex.In _value_i16 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) := h_499
          have h_500 : Litex.In _value_i16 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i16 h_499).1
                )
            )
          have h_501 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i16 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i16 h_499).2.1
                )
            )
          have h_502 : Litex.Le _value_i16 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i16 h_499).2.2
                )
            )
          have h_503 : Litex.In _value_i16 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i16 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_499)
                )
            )
          let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_504)
          have h_504 : Litex.In _value_i17 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) := h_504
          have h_505 : Litex.In _value_i17 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i17 h_504).1
                )
            )
          have h_506 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i17 h_504).2.1
                )
            )
          have h_507 : Litex.Le _value_i17 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i17 h_504).2.2
                )
            )
          have h_508 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_504)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i4 _value_i4 _object_h49 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h49
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_49))))) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_31 h_33)
    exact (show Litex.In _value_i5 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i22 : M.Value) (_raw_i23 : M.Value), M.mem _raw_i22 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))) → M.mem _raw_i23 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))) → ((fun (_raw_i22 : M.Value) (_raw_i23 : M.Value) => True) _raw_i22 _raw_i23) → True := (by
          intro _raw_i22 _raw_i23 h_823 h_828 _
          let _value_i22 := Litex.semanticObject (M := M) _raw_i22 (M.member_isSet h_823)
          have h_823 : Litex.In _value_i22 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) := h_823
          have h_824 : Litex.In _value_i22 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i22 h_823).1
                )
            )
          have h_825 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i22 h_823).2.1
                )
            )
          have h_826 : Litex.Le _value_i22 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i22 h_823).2.2
                )
            )
          have h_827 : Litex.In _value_i22 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i22 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_823)
                )
            )
          let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_828)
          have h_828 : Litex.In _value_i23 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) := h_828
          have h_829 : Litex.In _value_i23 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i23 h_828).1
                )
            )
          have h_830 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i23 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i23 h_828).2.1
                )
            )
          have h_831 : Litex.Le _value_i23 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i23 h_828).2.2
                )
            )
          have h_832 : Litex.In _value_i23 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i23 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_828)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i22 : M.Value) (_raw_i23 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i5 _value_i5 _object_h68 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h68
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_68))))));
  (let _litex_call_arg_0 := _value_i6;
  let _litex_call_arg_1 := _value_i7;
  Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixMultiplyInRealFnSet _litex_matrix_head (by
    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i24 : M.Value) (_raw_i25 : M.Value), M.mem _raw_i24 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))) → M.mem _raw_i25 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))) → ((fun (_raw_i24 : M.Value) (_raw_i25 : M.Value) => True) _raw_i24 _raw_i25) → True := (by
        intro _raw_i24 _raw_i25 h_926 h_931 _
        let _value_i24 := Litex.semanticObject (M := M) _raw_i24 (M.member_isSet h_926)
        have h_926 : Litex.In _value_i24 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) := h_926
        have h_927 : Litex.In _value_i24 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i24 h_926).1
              )
          )
        have h_928 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i24 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i24 h_926).2.1
              )
          )
        have h_929 : Litex.Le _value_i24 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i24 h_926).2.2
              )
          )
        have h_930 : Litex.In _value_i24 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i24 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_926)
              )
          )
        let _value_i25 := Litex.semanticObject (M := M) _raw_i25 (M.member_isSet h_931)
        have h_931 : Litex.In _value_i25 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) := h_931
        have h_932 : Litex.In _value_i25 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i25 h_931).1
              )
          )
        have h_933 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i25 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i25 h_931).2.1
              )
          )
        have h_934 : Litex.Le _value_i25 _value_i2 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i25 h_931).2.2
              )
          )
        have h_935 : Litex.In _value_i25 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i25 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_931)
              )
          )
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i24 : M.Value) (_raw_i25 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
    exact (Litex.inOfSame _value_i4 _value_i4 _object_h49 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h49
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_49)) (by
    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i26 : M.Value) (_raw_i27 : M.Value), M.mem _raw_i26 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))) → M.mem _raw_i27 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))) → ((fun (_raw_i26 : M.Value) (_raw_i27 : M.Value) => True) _raw_i26 _raw_i27) → True := (by
        intro _raw_i26 _raw_i27 h_1025 h_1030 _
        let _value_i26 := Litex.semanticObject (M := M) _raw_i26 (M.member_isSet h_1025)
        have h_1025 : Litex.In _value_i26 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) := h_1025
        have h_1026 : Litex.In _value_i26 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i26 h_1025).1
              )
          )
        have h_1027 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i26 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i26 h_1025).2.1
              )
          )
        have h_1028 : Litex.Le _value_i26 _value_i2 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i26 h_1025).2.2
              )
          )
        have h_1029 : Litex.In _value_i26 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i26 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1025)
              )
          )
        let _value_i27 := Litex.semanticObject (M := M) _raw_i27 (M.member_isSet h_1030)
        have h_1030 : Litex.In _value_i27 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) := h_1030
        have h_1031 : Litex.In _value_i27 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i27 h_1030).1
              )
          )
        have h_1032 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i27 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i27 h_1030).2.1
              )
          )
        have h_1033 : Litex.Le _value_i27 _value_i3 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i27 h_1030).2.2
              )
          )
        have h_1034 : Litex.In _value_i27 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i27 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1030)
              )
          )
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))
      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i26 : M.Value) (_raw_i27 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
    exact (Litex.inOfSame _value_i5 _value_i5 _object_h68 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h68
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_68))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
    exact h_112) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
    exact h_177)), True.intro⟩)))
  exact (by
    let _atomic_wd_1_0 := _object_w20
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_29 _Host_i2 _rep_i2 _value_i2 h_31 _Host_i3 _rep_i3 _value_i3 h_33 _Host_i4 _rep_i4 _value_i4 h_48 _Host_i5 _rep_i5 _value_i5 h_67 _Host_i6 _rep_i6 _value_i6 h_112 _Host_i7 _rep_i7 _value_i7 h_177
          have h_30 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_29)
                )
            )
          have h_32 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_31)
                )
            )
          have h_34 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i3 h_33)
                )
            )
          let _object_h49 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_29 h_31)))
          have h_49 : Litex.In _value_i4 _object_h49 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_29 h_31) _object_h49 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_29 h_31))) h_48)
                )
            )
          let _object_h68 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.R (M := M))) h_31 h_33)))
          have h_68 : Litex.In _value_i5 _object_h68 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i5 _value_i5 (Litex.matrixSet (Litex.R (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.R (M := M))) h_31 h_33) _object_h68 (Litex.sameRefl _value_i5) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.R (M := M))) h_31 h_33))) h_67)
                )
            )
          have h_113 : Litex.In _value_i6 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i6 h_112).1
                )
            )
          have h_114 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i6 h_112).2.1
                )
            )
          have h_115 : Litex.Le _value_i6 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i6 h_112).2.2
                )
            )
          have h_116 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_112)
                )
            )
          have h_178 : Litex.In _value_i7 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i7 h_177).1
                )
            )
          have h_179 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i7 h_177).2.1
                )
            )
          have h_180 : Litex.Le _value_i7 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i7 h_177).2.2
                )
            )
          have h_181 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_177)
                )
            )
          let _object_w20 := (let _litex_matrix_head := (Litex.matrixMultiply _value_i4 _value_i5 _value_i1 _value_i2 _value_i3 h_29 h_31 h_33 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_29 h_31)
            exact (show Litex.In _value_i4 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i16 : M.Value) (_raw_i17 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))) → M.mem _raw_i17 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))) → ((fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True) _raw_i16 _raw_i17) → True := (by
                  intro _raw_i16 _raw_i17 h_499 h_504 _
                  let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_499)
                  have h_499 : Litex.In _value_i16 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) := h_499
                  have h_500 : Litex.In _value_i16 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i16 h_499).1
                        )
                    )
                  have h_501 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i16 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i16 h_499).2.1
                        )
                    )
                  have h_502 : Litex.Le _value_i16 _value_i1 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i16 h_499).2.2
                        )
                    )
                  have h_503 : Litex.In _value_i16 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i16 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_499)
                        )
                    )
                  let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_504)
                  have h_504 : Litex.In _value_i17 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) := h_504
                  have h_505 : Litex.In _value_i17 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i17 h_504).1
                        )
                    )
                  have h_506 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i17 h_504).2.1
                        )
                    )
                  have h_507 : Litex.Le _value_i17 _value_i2 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i17 h_504).2.2
                        )
                    )
                  have h_508 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_504)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i4 _value_i4 _object_h49 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h49
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_49))))) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_31 h_33)
            exact (show Litex.In _value_i5 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i22 : M.Value) (_raw_i23 : M.Value), M.mem _raw_i22 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))) → M.mem _raw_i23 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))) → ((fun (_raw_i22 : M.Value) (_raw_i23 : M.Value) => True) _raw_i22 _raw_i23) → True := (by
                  intro _raw_i22 _raw_i23 h_823 h_828 _
                  let _value_i22 := Litex.semanticObject (M := M) _raw_i22 (M.member_isSet h_823)
                  have h_823 : Litex.In _value_i22 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) := h_823
                  have h_824 : Litex.In _value_i22 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i22 h_823).1
                        )
                    )
                  have h_825 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i22 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i22 h_823).2.1
                        )
                    )
                  have h_826 : Litex.Le _value_i22 _value_i2 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i22 h_823).2.2
                        )
                    )
                  have h_827 : Litex.In _value_i22 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i22 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_823)
                        )
                    )
                  let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_828)
                  have h_828 : Litex.In _value_i23 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) := h_828
                  have h_829 : Litex.In _value_i23 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i23 h_828).1
                        )
                    )
                  have h_830 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i23 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i23 h_828).2.1
                        )
                    )
                  have h_831 : Litex.Le _value_i23 _value_i3 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i23 h_828).2.2
                        )
                    )
                  have h_832 : Litex.In _value_i23 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i23 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_828)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i22 : M.Value) (_raw_i23 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i5 _value_i5 _object_h68 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h68
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_68))))));
          (let _litex_call_arg_0 := _value_i6;
          let _litex_call_arg_1 := _value_i7;
          Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixMultiplyInRealFnSet _litex_matrix_head (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i24 : M.Value) (_raw_i25 : M.Value), M.mem _raw_i24 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))) → M.mem _raw_i25 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))) → ((fun (_raw_i24 : M.Value) (_raw_i25 : M.Value) => True) _raw_i24 _raw_i25) → True := (by
                intro _raw_i24 _raw_i25 h_926 h_931 _
                let _value_i24 := Litex.semanticObject (M := M) _raw_i24 (M.member_isSet h_926)
                have h_926 : Litex.In _value_i24 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) := h_926
                have h_927 : Litex.In _value_i24 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i24 h_926).1
                      )
                  )
                have h_928 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i24 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i24 h_926).2.1
                      )
                  )
                have h_929 : Litex.Le _value_i24 _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i24 h_926).2.2
                      )
                  )
                have h_930 : Litex.In _value_i24 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i24 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_926)
                      )
                  )
                let _value_i25 := Litex.semanticObject (M := M) _raw_i25 (M.member_isSet h_931)
                have h_931 : Litex.In _value_i25 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) := h_931
                have h_932 : Litex.In _value_i25 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i25 h_931).1
                      )
                  )
                have h_933 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i25 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i25 h_931).2.1
                      )
                  )
                have h_934 : Litex.Le _value_i25 _value_i2 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i25 h_931).2.2
                      )
                  )
                have h_935 : Litex.In _value_i25 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i25 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_931)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))] (by
              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i24 : M.Value) (_raw_i25 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
            exact (Litex.inOfSame _value_i4 _value_i4 _object_h49 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h49
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_49)) (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i26 : M.Value) (_raw_i27 : M.Value), M.mem _raw_i26 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))) → M.mem _raw_i27 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))) → ((fun (_raw_i26 : M.Value) (_raw_i27 : M.Value) => True) _raw_i26 _raw_i27) → True := (by
                intro _raw_i26 _raw_i27 h_1025 h_1030 _
                let _value_i26 := Litex.semanticObject (M := M) _raw_i26 (M.member_isSet h_1025)
                have h_1025 : Litex.In _value_i26 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) := h_1025
                have h_1026 : Litex.In _value_i26 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i26 h_1025).1
                      )
                  )
                have h_1027 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i26 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i26 h_1025).2.1
                      )
                  )
                have h_1028 : Litex.Le _value_i26 _value_i2 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i26 h_1025).2.2
                      )
                  )
                have h_1029 : Litex.In _value_i26 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i26 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1025)
                      )
                  )
                let _value_i27 := Litex.semanticObject (M := M) _raw_i27 (M.member_isSet h_1030)
                have h_1030 : Litex.In _value_i27 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) := h_1030
                have h_1031 : Litex.In _value_i27 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i27 h_1030).1
                      )
                  )
                have h_1032 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i27 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i27 h_1030).2.1
                      )
                  )
                have h_1033 : Litex.Le _value_i27 _value_i3 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i27 h_1030).2.2
                      )
                  )
                have h_1034 : Litex.In _value_i27 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i27 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1030)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))
              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i26 : M.Value) (_raw_i27 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
            exact (Litex.inOfSame _value_i5 _value_i5 _object_h68 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h68
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_68))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
            exact h_112) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
            exact h_177)), True.intro⟩)))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w20
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w20
                    exact (show Litex.In _atomic_wd_1_0 (Litex.R (M := M)) from (let _litex_matrix_signature := (Litex.matrixEntrywiseSignature ((_atomic_wd_1_0).val.function).val.rows ((_atomic_wd_1_0).val.function).val.cols .real); Litex.FunctionSemantics.call_mem _litex_matrix_signature.domain _litex_matrix_signature.output (Litex.denote (_atomic_wd_1_0).val.function) (Litex.denote (Litex.callArguments2 _value_i6 _value_i7)) (let _litex_matrix := (_atomic_wd_1_0).val.function; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixMultiplyInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i31 : M.Value) (_raw_i32 : M.Value), M.mem _raw_i31 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))) → M.mem _raw_i32 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))) → ((fun (_raw_i31 : M.Value) (_raw_i32 : M.Value) => True) _raw_i31 _raw_i32) → True := (by
                          intro _raw_i31 _raw_i32 h_1419 h_1424 _
                          let _value_i31 := Litex.semanticObject (M := M) _raw_i31 (M.member_isSet h_1419)
                          have h_1419 : Litex.In _value_i31 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) := h_1419
                          have h_1420 : Litex.In _value_i31 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i31 h_1419).1
                                )
                            )
                          have h_1421 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i31 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i31 h_1419).2.1
                                )
                            )
                          have h_1422 : Litex.Le _value_i31 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i31 h_1419).2.2
                                )
                            )
                          have h_1423 : Litex.In _value_i31 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)) _value_i31 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1419)
                                )
                            )
                          let _value_i32 := Litex.semanticObject (M := M) _raw_i32 (M.member_isSet h_1424)
                          have h_1424 : Litex.In _value_i32 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) := h_1424
                          have h_1425 : Litex.In _value_i32 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i32 h_1424).1
                                )
                            )
                          have h_1426 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i32 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i32 h_1424).2.1
                                )
                            )
                          have h_1427 : Litex.Le _value_i32 _value_i2 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i32 h_1424).2.2
                                )
                            )
                          have h_1428 : Litex.In _value_i32 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i32 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1424)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i31 : M.Value) (_raw_i32 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i4 _value_i4 _object_h49 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h49
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_49)) (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i33 : M.Value) (_raw_i34 : M.Value), M.mem _raw_i33 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))) → M.mem _raw_i34 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))) → ((fun (_raw_i33 : M.Value) (_raw_i34 : M.Value) => True) _raw_i33 _raw_i34) → True := (by
                          intro _raw_i33 _raw_i34 h_1518 h_1523 _
                          let _value_i33 := Litex.semanticObject (M := M) _raw_i33 (M.member_isSet h_1518)
                          have h_1518 : Litex.In _value_i33 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) := h_1518
                          have h_1519 : Litex.In _value_i33 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i33 h_1518).1
                                )
                            )
                          have h_1520 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i33 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i33 h_1518).2.1
                                )
                            )
                          have h_1521 : Litex.Le _value_i33 _value_i2 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i33 h_1518).2.2
                                )
                            )
                          have h_1522 : Litex.In _value_i33 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)) _value_i33 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1518)
                                )
                            )
                          let _value_i34 := Litex.semanticObject (M := M) _raw_i34 (M.member_isSet h_1523)
                          have h_1523 : Litex.In _value_i34 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) := h_1523
                          have h_1524 : Litex.In _value_i34 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i34 h_1523).1
                                )
                            )
                          have h_1525 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i34 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i34 h_1523).2.1
                                )
                            )
                          have h_1526 : Litex.Le _value_i34 _value_i3 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i34 h_1523).2.2
                                )
                            )
                          have h_1527 : Litex.In _value_i34 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)) _value_i34 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1523)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_31)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i33 : M.Value) (_raw_i34 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i5 _value_i5 _object_h68 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h68
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_68)))) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))) (fun (_litex_input : M.Value) => (fun (_raw_i35 : M.Value) (_raw_i36 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i6 _value_i7))).mpr ⟨(Litex.callArguments2_mem_cart _value_i6 _value_i7 (by
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_29))
                      exact h_112) (by
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i3 h_33))
                      exact h_177)), True.intro⟩))))
                )
            )
          exact h_1
        )
      )
  )

theorem h_1547 : ∀ {_Host_i38 : Type v38} [_rep_i38 : Litex.Representation M _Host_i38] (_value_i38 : Litex.Obj (M := M) _Host_i38) (h_1570 : Litex.In _value_i38 (Litex.N (M := M))) {_Host_i39 : Type v39} [_rep_i39 : Litex.Representation M _Host_i39] (_value_i39 : Litex.Obj (M := M) _Host_i39) (h_1572 : Litex.In _value_i39 (Litex.N (M := M))) {_Host_i40 : Type v40} [_rep_i40 : Litex.Representation M _Host_i40] (_value_i40 : Litex.Obj (M := M) _Host_i40) (h_1587 : Litex.In _value_i40 (Litex.matrixSet (Litex.R (M := M)) _value_i38 _value_i39 (Litex.isSet (Litex.R (M := M))) h_1570 h_1572)) {_Host_i41 : Type v41} [_rep_i41 : Litex.Representation M _Host_i41] (_value_i41 : Litex.Obj (M := M) _Host_i41) (h_1597 : Litex.In _value_i41 (Litex.finiteSeq (Litex.R (M := M)) _value_i39 (Litex.isSet (Litex.R (M := M))) h_1572)) {_Host_i42 : Type v42} [_rep_i42 : Litex.Representation M _Host_i42] (_value_i42 : Litex.Obj (M := M) _Host_i42) (h_1637 : Litex.In _value_i42 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))), (by
  let _object_h1588 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i38 _value_i39 (Litex.isSet (Litex.R (M := M))) h_1570 h_1572)))
  have h_1588 : Litex.In _value_i40 _object_h1588 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i40 _value_i40 (Litex.matrixSet (Litex.R (M := M)) _value_i38 _value_i39 (Litex.isSet (Litex.R (M := M))) h_1570 h_1572) _object_h1588 (Litex.sameRefl _value_i40) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i38 _value_i39 (Litex.isSet (Litex.R (M := M))) h_1570 h_1572))) h_1587)
        )
    )
  let _object_h1598 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) _value_i39 (Litex.isSet (Litex.R (M := M))) h_1572)))
  have h_1598 : Litex.In _value_i41 _object_h1598 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i41 _value_i41 (Litex.finiteSeq (Litex.R (M := M)) _value_i39 (Litex.isSet (Litex.R (M := M))) h_1572) _object_h1598 (Litex.sameRefl _value_i41) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i39 (Litex.isSet (Litex.R (M := M))) h_1572)) h_1597)
        )
    )
  let _object_w42 := (let _litex_matrix_head := (Litex.matrixApply _value_i40 _value_i41 _value_i38 _value_i39 h_1570 h_1572 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i38 _value_i39 (Litex.isSet (Litex.C (M := M))) h_1570 h_1572)
    exact (show Litex.In _value_i40 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i50 : M.Value) (_raw_i51 : M.Value), M.mem _raw_i50 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))) → M.mem _raw_i51 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) → ((fun (_raw_i50 : M.Value) (_raw_i51 : M.Value) => True) _raw_i50 _raw_i51) → True := (by
          intro _raw_i50 _raw_i51 h_1878 h_1883 _
          let _value_i50 := Litex.semanticObject (M := M) _raw_i50 (M.member_isSet h_1878)
          have h_1878 : Litex.In _value_i50 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) := h_1878
          have h_1879 : Litex.In _value_i50 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i50 h_1878).1
                )
            )
          have h_1880 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i50 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i50 h_1878).2.1
                )
            )
          have h_1881 : Litex.Le _value_i50 _value_i38 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i50 h_1878).2.2
                )
            )
          have h_1882 : Litex.In _value_i50 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i50 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1878)
                )
            )
          let _value_i51 := Litex.semanticObject (M := M) _raw_i51 (M.member_isSet h_1883)
          have h_1883 : Litex.In _value_i51 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) := h_1883
          have h_1884 : Litex.In _value_i51 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i51 h_1883).1
                )
            )
          have h_1885 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i51 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i51 h_1883).2.1
                )
            )
          have h_1886 : Litex.Le _value_i51 _value_i39 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i51 h_1883).2.2
                )
            )
          have h_1887 : Litex.In _value_i51 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i51 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1883)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i50 : M.Value) (_raw_i51 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i40 _value_i40 _object_h1588 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h1588
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_1588))))) (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i39 (Litex.isSet (Litex.C (M := M))) h_1572)
    exact (by
      let _membership_function := _value_i41
      let _membership_target := (let _checked_header : ∀ (_raw_i53 : M.Value), M.mem _raw_i53 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) → ((fun (_raw_i53 : M.Value) => True) _raw_i53) → True := (by
          intro _raw_i53 h_2007 _
          let _value_i53 := Litex.semanticObject (M := M) _raw_i53 (M.member_isSet h_2007)
          have h_2007 : Litex.In _value_i53 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) := h_2007
          have h_2008 : Litex.In _value_i53 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 h_2007).1
                )
            )
          have h_2009 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i53 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 h_2007).2.1
                )
            )
          have h_2010 : Litex.Le _value_i53 _value_i39 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 h_2007).2.2
                )
            )
          have h_2011 : Litex.In _value_i53 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2007)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i53 : M.Value) => True) _litex_input)))
      have h_2012 : ∀ {_Host_i53 : Type _} [_rep_i53 : Litex.Representation M _Host_i53] (_value_i53 : Litex.Obj (M := M) _Host_i53) (h_2408 : Litex.In _value_i53 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))), (by
        let _object_w36 := (let _litex_call_arg_0 := _value_i53;
        Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) => True) _litex_input) _value_i41 _litex_call_arg_0 h_1598 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))
          exact h_2408) True.intro)
        exact (by
          let _atomic_wd_2_0 := _object_w36
          exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
      ) := (by
        intro _Host_i53 _rep_i53 _value_i53 h_2408
        have h_2409 : Litex.In _value_i53 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 h_2408).1
              )
          )
        have h_2410 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i53 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 h_2408).2.1
              )
          )
        have h_2411 : Litex.Le _value_i53 _value_i39 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 h_2408).2.2
              )
          )
        have h_2412 : Litex.In _value_i53 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2408)
              )
          )
        let _object_w36 := (let _litex_call_arg_0 := _value_i53;
        Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) => True) _litex_input) _value_i41 _litex_call_arg_0 h_1598 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))
          exact h_2408) True.intro)
        have h_2013 : (by
          let _atomic_wd_2_0 := _object_w36
          exact Litex.In _atomic_wd_2_0 (Litex.C (M := M))) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  let _atomic_wd_2_0 := _object_w36
                  exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callOnInOutput _atomic_wd_2_0)))
              )
          )
        exact h_2013
      )
      exact (by
        let _source_signature := (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i54 : M.Value) => True) _litex_input))
        have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame _value_i41 _value_i41 (Litex.finiteSeq (Litex.R (M := M)) _value_i39 (Litex.isSet (Litex.R (M := M))) h_1572) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i54 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i39 (Litex.isSet (Litex.R (M := M))) h_1572))) h_1597)
        have _same_domain : _source_signature.domain = _membership_target.val.domain := (by rfl)
        change M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _membership_target.val.domain _membership_target.val.output)
        have _source_graph : M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _source_signature.domain _source_signature.output) := _source_member
        rw [_same_domain] at _source_graph
        apply Litex.FunctionSemantics.fnSet_of_returns _source_graph
        intro _input _hin
        change M.mem _input (Litex.SetSemantics.sepValue _ _) at _hin
        obtain ⟨_members, _guard⟩ := (Litex.SetSemantics.sep_members _ _ _).mp _hin
        let _raw_0 := _input
        have _member_0 := _members
        let _arg_0 := Litex.semanticObject (M := M) _raw_0 (M.member_isSet _member_0)
        exact h_2012 _arg_0 _member_0))));
  (let _litex_call_arg_0 := _value_i42;
  Litex.callOn (Litex.matrixApplySignature (_litex_matrix_head).val.rows .real) _litex_matrix_head _litex_call_arg_0 (Litex.matrixApplyInRealFnSet _litex_matrix_head (by
    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i55 : M.Value) (_raw_i56 : M.Value), M.mem _raw_i55 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))) → M.mem _raw_i56 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) → ((fun (_raw_i55 : M.Value) (_raw_i56 : M.Value) => True) _raw_i55 _raw_i56) → True := (by
        intro _raw_i55 _raw_i56 h_2728 h_2733 _
        let _value_i55 := Litex.semanticObject (M := M) _raw_i55 (M.member_isSet h_2728)
        have h_2728 : Litex.In _value_i55 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) := h_2728
        have h_2729 : Litex.In _value_i55 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i55 h_2728).1
              )
          )
        have h_2730 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i55 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i55 h_2728).2.1
              )
          )
        have h_2731 : Litex.Le _value_i55 _value_i38 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i55 h_2728).2.2
              )
          )
        have h_2732 : Litex.In _value_i55 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i55 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2728)
              )
          )
        let _value_i56 := Litex.semanticObject (M := M) _raw_i56 (M.member_isSet h_2733)
        have h_2733 : Litex.In _value_i56 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) := h_2733
        have h_2734 : Litex.In _value_i56 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i56 h_2733).1
              )
          )
        have h_2735 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i56 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i56 h_2733).2.1
              )
          )
        have h_2736 : Litex.Le _value_i56 _value_i39 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i56 h_2733).2.2
              )
          )
        have h_2737 : Litex.In _value_i56 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i56 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2733)
              )
          )
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)))
      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i55 : M.Value) (_raw_i56 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
    exact (Litex.inOfSame _value_i40 _value_i40 _object_h1588 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h1588
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_1588)) (by
    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i57 : M.Value), M.mem _raw_i57 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) → ((fun (_raw_i57 : M.Value) => True) _raw_i57) → True := (by
        intro _raw_i57 h_2805 _
        let _value_i57 := Litex.semanticObject (M := M) _raw_i57 (M.member_isSet h_2805)
        have h_2805 : Litex.In _value_i57 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) := h_2805
        have h_2806 : Litex.In _value_i57 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i57 h_2805).1
              )
          )
        have h_2807 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i57 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i57 h_2805).2.1
              )
          )
        have h_2808 : Litex.Le _value_i57 _value_i39 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i57 h_2805).2.2
              )
          )
        have h_2809 : Litex.In _value_i57 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i57 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2805)
              )
          )
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i57 : M.Value) => True) _litex_input)))
    exact (Litex.inOfSame _value_i41 _value_i41 _object_h1598 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h1598
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_1598))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))
    exact h_1637), True.intro⟩)))
  exact (by
    let _atomic_wd_1_0 := _object_w42
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i38 _rep_i38 _value_i38 h_1570 _Host_i39 _rep_i39 _value_i39 h_1572 _Host_i40 _rep_i40 _value_i40 h_1587 _Host_i41 _rep_i41 _value_i41 h_1597 _Host_i42 _rep_i42 _value_i42 h_1637
          have h_1571 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i38 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i38 h_1570)
                )
            )
          have h_1573 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i39 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i39 h_1572)
                )
            )
          let _object_h1588 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i38 _value_i39 (Litex.isSet (Litex.R (M := M))) h_1570 h_1572)))
          have h_1588 : Litex.In _value_i40 _object_h1588 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i40 _value_i40 (Litex.matrixSet (Litex.R (M := M)) _value_i38 _value_i39 (Litex.isSet (Litex.R (M := M))) h_1570 h_1572) _object_h1588 (Litex.sameRefl _value_i40) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i38 _value_i39 (Litex.isSet (Litex.R (M := M))) h_1570 h_1572))) h_1587)
                )
            )
          let _object_h1598 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) _value_i39 (Litex.isSet (Litex.R (M := M))) h_1572)))
          have h_1598 : Litex.In _value_i41 _object_h1598 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i41 _value_i41 (Litex.finiteSeq (Litex.R (M := M)) _value_i39 (Litex.isSet (Litex.R (M := M))) h_1572) _object_h1598 (Litex.sameRefl _value_i41) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i39 (Litex.isSet (Litex.R (M := M))) h_1572)) h_1597)
                )
            )
          have h_1638 : Litex.In _value_i42 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i42 h_1637).1
                )
            )
          have h_1639 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i42 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i42 h_1637).2.1
                )
            )
          have h_1640 : Litex.Le _value_i42 _value_i38 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i42 h_1637).2.2
                )
            )
          have h_1641 : Litex.In _value_i42 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i42 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1637)
                )
            )
          let _object_w42 := (let _litex_matrix_head := (Litex.matrixApply _value_i40 _value_i41 _value_i38 _value_i39 h_1570 h_1572 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i38 _value_i39 (Litex.isSet (Litex.C (M := M))) h_1570 h_1572)
            exact (show Litex.In _value_i40 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i50 : M.Value) (_raw_i51 : M.Value), M.mem _raw_i50 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))) → M.mem _raw_i51 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) → ((fun (_raw_i50 : M.Value) (_raw_i51 : M.Value) => True) _raw_i50 _raw_i51) → True := (by
                  intro _raw_i50 _raw_i51 h_1878 h_1883 _
                  let _value_i50 := Litex.semanticObject (M := M) _raw_i50 (M.member_isSet h_1878)
                  have h_1878 : Litex.In _value_i50 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) := h_1878
                  have h_1879 : Litex.In _value_i50 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i50 h_1878).1
                        )
                    )
                  have h_1880 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i50 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i50 h_1878).2.1
                        )
                    )
                  have h_1881 : Litex.Le _value_i50 _value_i38 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i50 h_1878).2.2
                        )
                    )
                  have h_1882 : Litex.In _value_i50 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i50 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1878)
                        )
                    )
                  let _value_i51 := Litex.semanticObject (M := M) _raw_i51 (M.member_isSet h_1883)
                  have h_1883 : Litex.In _value_i51 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) := h_1883
                  have h_1884 : Litex.In _value_i51 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i51 h_1883).1
                        )
                    )
                  have h_1885 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i51 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i51 h_1883).2.1
                        )
                    )
                  have h_1886 : Litex.Le _value_i51 _value_i39 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i51 h_1883).2.2
                        )
                    )
                  have h_1887 : Litex.In _value_i51 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i51 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1883)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i50 : M.Value) (_raw_i51 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i40 _value_i40 _object_h1588 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h1588
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_1588))))) (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i39 (Litex.isSet (Litex.C (M := M))) h_1572)
            exact (by
              let _membership_function := _value_i41
              let _membership_target := (let _checked_header : ∀ (_raw_i53 : M.Value), M.mem _raw_i53 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) → ((fun (_raw_i53 : M.Value) => True) _raw_i53) → True := (by
                  intro _raw_i53 h_2007 _
                  let _value_i53 := Litex.semanticObject (M := M) _raw_i53 (M.member_isSet h_2007)
                  have h_2007 : Litex.In _value_i53 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) := h_2007
                  have h_2008 : Litex.In _value_i53 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 h_2007).1
                        )
                    )
                  have h_2009 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i53 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 h_2007).2.1
                        )
                    )
                  have h_2010 : Litex.Le _value_i53 _value_i39 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 h_2007).2.2
                        )
                    )
                  have h_2011 : Litex.In _value_i53 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2007)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i53 : M.Value) => True) _litex_input)))
              have h_2012 : ∀ {_Host_i53 : Type _} [_rep_i53 : Litex.Representation M _Host_i53] (_value_i53 : Litex.Obj (M := M) _Host_i53) (h_2408 : Litex.In _value_i53 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))), (by
                let _object_w36 := (let _litex_call_arg_0 := _value_i53;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) => True) _litex_input) _value_i41 _litex_call_arg_0 h_1598 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))
                  exact h_2408) True.intro)
                exact (by
                  let _atomic_wd_2_0 := _object_w36
                  exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
              ) := (by
                intro _Host_i53 _rep_i53 _value_i53 h_2408
                have h_2409 : Litex.In _value_i53 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 h_2408).1
                      )
                  )
                have h_2410 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i53 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 h_2408).2.1
                      )
                  )
                have h_2411 : Litex.Le _value_i53 _value_i39 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 h_2408).2.2
                      )
                  )
                have h_2412 : Litex.In _value_i53 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i53 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2408)
                      )
                  )
                let _object_w36 := (let _litex_call_arg_0 := _value_i53;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) => True) _litex_input) _value_i41 _litex_call_arg_0 h_1598 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))
                  exact h_2408) True.intro)
                have h_2013 : (by
                  let _atomic_wd_2_0 := _object_w36
                  exact Litex.In _atomic_wd_2_0 (Litex.C (M := M))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_2_0 := _object_w36
                          exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callOnInOutput _atomic_wd_2_0)))
                      )
                  )
                exact h_2013
              )
              exact (by
                let _source_signature := (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i54 : M.Value) => True) _litex_input))
                have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame _value_i41 _value_i41 (Litex.finiteSeq (Litex.R (M := M)) _value_i39 (Litex.isSet (Litex.R (M := M))) h_1572) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i54 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i39 (Litex.isSet (Litex.R (M := M))) h_1572))) h_1597)
                have _same_domain : _source_signature.domain = _membership_target.val.domain := (by rfl)
                change M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _membership_target.val.domain _membership_target.val.output)
                have _source_graph : M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _source_signature.domain _source_signature.output) := _source_member
                rw [_same_domain] at _source_graph
                apply Litex.FunctionSemantics.fnSet_of_returns _source_graph
                intro _input _hin
                change M.mem _input (Litex.SetSemantics.sepValue _ _) at _hin
                obtain ⟨_members, _guard⟩ := (Litex.SetSemantics.sep_members _ _ _).mp _hin
                let _raw_0 := _input
                have _member_0 := _members
                let _arg_0 := Litex.semanticObject (M := M) _raw_0 (M.member_isSet _member_0)
                exact h_2012 _arg_0 _member_0))));
          (let _litex_call_arg_0 := _value_i42;
          Litex.callOn (Litex.matrixApplySignature (_litex_matrix_head).val.rows .real) _litex_matrix_head _litex_call_arg_0 (Litex.matrixApplyInRealFnSet _litex_matrix_head (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i55 : M.Value) (_raw_i56 : M.Value), M.mem _raw_i55 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))) → M.mem _raw_i56 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) → ((fun (_raw_i55 : M.Value) (_raw_i56 : M.Value) => True) _raw_i55 _raw_i56) → True := (by
                intro _raw_i55 _raw_i56 h_2728 h_2733 _
                let _value_i55 := Litex.semanticObject (M := M) _raw_i55 (M.member_isSet h_2728)
                have h_2728 : Litex.In _value_i55 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) := h_2728
                have h_2729 : Litex.In _value_i55 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i55 h_2728).1
                      )
                  )
                have h_2730 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i55 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i55 h_2728).2.1
                      )
                  )
                have h_2731 : Litex.Le _value_i55 _value_i38 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i55 h_2728).2.2
                      )
                  )
                have h_2732 : Litex.In _value_i55 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i55 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2728)
                      )
                  )
                let _value_i56 := Litex.semanticObject (M := M) _raw_i56 (M.member_isSet h_2733)
                have h_2733 : Litex.In _value_i56 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) := h_2733
                have h_2734 : Litex.In _value_i56 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i56 h_2733).1
                      )
                  )
                have h_2735 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i56 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i56 h_2733).2.1
                      )
                  )
                have h_2736 : Litex.Le _value_i56 _value_i39 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i56 h_2733).2.2
                      )
                  )
                have h_2737 : Litex.In _value_i56 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i56 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2733)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))] (by
              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)))
              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i55 : M.Value) (_raw_i56 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
            exact (Litex.inOfSame _value_i40 _value_i40 _object_h1588 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h1588
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_1588)) (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i57 : M.Value), M.mem _raw_i57 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) → ((fun (_raw_i57 : M.Value) => True) _raw_i57) → True := (by
                intro _raw_i57 h_2805 _
                let _value_i57 := Litex.semanticObject (M := M) _raw_i57 (M.member_isSet h_2805)
                have h_2805 : Litex.In _value_i57 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) := h_2805
                have h_2806 : Litex.In _value_i57 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i57 h_2805).1
                      )
                  )
                have h_2807 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i57 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i57 h_2805).2.1
                      )
                  )
                have h_2808 : Litex.Le _value_i57 _value_i39 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i57 h_2805).2.2
                      )
                  )
                have h_2809 : Litex.In _value_i57 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i57 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2805)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i57 : M.Value) => True) _litex_input)))
            exact (Litex.inOfSame _value_i41 _value_i41 _object_h1598 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h1598
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_1598))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))
            exact h_1637), True.intro⟩)))
          have h_1546 : (by
            let _atomic_wd_1_0 := _object_w42
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w42
                    exact (show Litex.In _atomic_wd_1_0 (Litex.R (M := M)) from (let _litex_matrix_signature := (Litex.matrixApplySignature ((_atomic_wd_1_0).val.function).val.rows .real); Litex.FunctionSemantics.call_mem _litex_matrix_signature.domain _litex_matrix_signature.output (Litex.denote (_atomic_wd_1_0).val.function) (Litex.denote _value_i42) (let _litex_matrix := (_atomic_wd_1_0).val.function; let _litex_matrix_signature := (Litex.matrixApplySignature (_litex_matrix).val.rows .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixApplyInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i60 : M.Value) (_raw_i61 : M.Value), M.mem _raw_i60 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))) → M.mem _raw_i61 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) → ((fun (_raw_i60 : M.Value) (_raw_i61 : M.Value) => True) _raw_i60 _raw_i61) → True := (by
                          intro _raw_i60 _raw_i61 h_3073 h_3078 _
                          let _value_i60 := Litex.semanticObject (M := M) _raw_i60 (M.member_isSet h_3073)
                          have h_3073 : Litex.In _value_i60 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) := h_3073
                          have h_3074 : Litex.In _value_i60 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i60 h_3073).1
                                )
                            )
                          have h_3075 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i60 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i60 h_3073).2.1
                                )
                            )
                          have h_3076 : Litex.Le _value_i60 _value_i38 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i60 h_3073).2.2
                                )
                            )
                          have h_3077 : Litex.In _value_i60 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)) _value_i60 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3073)
                                )
                            )
                          let _value_i61 := Litex.semanticObject (M := M) _raw_i61 (M.member_isSet h_3078)
                          have h_3078 : Litex.In _value_i61 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) := h_3078
                          have h_3079 : Litex.In _value_i61 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i61 h_3078).1
                                )
                            )
                          have h_3080 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i61 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i61 h_3078).2.1
                                )
                            )
                          have h_3081 : Litex.Le _value_i61 _value_i39 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i61 h_3078).2.2
                                )
                            )
                          have h_3082 : Litex.In _value_i61 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i61 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3078)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i60 : M.Value) (_raw_i61 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i40 _value_i40 _object_h1588 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h1588
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_1588)) (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i62 : M.Value), M.mem _raw_i62 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) → ((fun (_raw_i62 : M.Value) => True) _raw_i62) → True := (by
                          intro _raw_i62 h_3150 _
                          let _value_i62 := Litex.semanticObject (M := M) _raw_i62 (M.member_isSet h_3150)
                          have h_3150 : Litex.In _value_i62 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) := h_3150
                          have h_3151 : Litex.In _value_i62 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i62 h_3150).1
                                )
                            )
                          have h_3152 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i62 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i62 h_3150).2.1
                                )
                            )
                          have h_3153 : Litex.Le _value_i62 _value_i39 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i62 h_3150).2.2
                                )
                            )
                          have h_3154 : Litex.In _value_i62 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572)) _value_i62 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3150)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i39 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i39 h_1572))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i62 : M.Value) => True) _litex_input)))
                      exact (Litex.inOfSame _value_i41 _value_i41 _object_h1598 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h1598
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_1598)))) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))) (fun (_litex_input : M.Value) => (fun (_raw_i63 : M.Value) => True) _litex_input) (Litex.denote _value_i42)).mpr ⟨(by
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i38 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i38 h_1570))
                      exact h_1637), True.intro⟩))))
                )
            )
          exact h_1546
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_product_x5f_real_x5f_values_x2f_statement_x2e_lit
