import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_entrywise_x5f_real_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v35 v36 v37 v38 v39 v40
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_25 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_27 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_42 : Litex.In _value_i3 (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27)) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_44 : Litex.In _value_i4 (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27)) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_84 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_143 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))), (by
  let _object_h43 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27)))
  have h_43 : Litex.In _value_i3 _object_h43 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27) _object_h43 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27))) h_42)
        )
    )
  let _object_h45 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27)))
  have h_45 : Litex.In _value_i4 _object_h45 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27) _object_h45 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27))) h_44)
        )
    )
  let _object_w11 := (let _litex_matrix_head := (Litex.matrixEntrywise .add _value_i3 _value_i4 _value_i1 _value_i2 h_25 h_27 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
    exact (show Litex.In _value_i3 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i15 : M.Value) (_raw_i16 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))) → M.mem _raw_i16 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))) → ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) _raw_i15 _raw_i16) → True := (by
          intro _raw_i15 _raw_i16 h_300 h_305 _
          let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_300)
          have h_300 : Litex.In _value_i15 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) := h_300
          have h_301 : Litex.In _value_i15 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i15 h_300).1
                )
            )
          have h_302 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i15 h_300).2.1
                )
            )
          have h_303 : Litex.Le _value_i15 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i15 h_300).2.2
                )
            )
          have h_304 : Litex.In _value_i15 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i15 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_300)
                )
            )
          let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_305)
          have h_305 : Litex.In _value_i16 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) := h_305
          have h_306 : Litex.In _value_i16 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i16 h_305).1
                )
            )
          have h_307 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i16 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i16 h_305).2.1
                )
            )
          have h_308 : Litex.Le _value_i16 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i16 h_305).2.2
                )
            )
          have h_309 : Litex.In _value_i16 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i16 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_305)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i3 _value_i3 _object_h43 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h43
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_43))))) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
    exact (show Litex.In _value_i4 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i21 : M.Value) (_raw_i22 : M.Value), M.mem _raw_i21 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))) → M.mem _raw_i22 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))) → ((fun (_raw_i21 : M.Value) (_raw_i22 : M.Value) => True) _raw_i21 _raw_i22) → True := (by
          intro _raw_i21 _raw_i22 h_462 h_467 _
          let _value_i21 := Litex.semanticObject (M := M) _raw_i21 (M.member_isSet h_462)
          have h_462 : Litex.In _value_i21 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) := h_462
          have h_463 : Litex.In _value_i21 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i21 h_462).1
                )
            )
          have h_464 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i21 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i21 h_462).2.1
                )
            )
          have h_465 : Litex.Le _value_i21 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i21 h_462).2.2
                )
            )
          have h_466 : Litex.In _value_i21 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i21 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_462)
                )
            )
          let _value_i22 := Litex.semanticObject (M := M) _raw_i22 (M.member_isSet h_467)
          have h_467 : Litex.In _value_i22 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) := h_467
          have h_468 : Litex.In _value_i22 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i22 h_467).1
                )
            )
          have h_469 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i22 h_467).2.1
                )
            )
          have h_470 : Litex.Le _value_i22 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i22 h_467).2.2
                )
            )
          have h_471 : Litex.In _value_i22 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i22 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_467)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i21 : M.Value) (_raw_i22 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i4 _value_i4 _object_h45 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h45
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_45))))));
  (let _litex_call_arg_0 := _value_i5;
  let _litex_call_arg_1 := _value_i6;
  Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixEntrywiseInRealFnSet _litex_matrix_head (by
    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i23 : M.Value) (_raw_i24 : M.Value), M.mem _raw_i23 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))) → M.mem _raw_i24 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))) → ((fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) _raw_i23 _raw_i24) → True := (by
        intro _raw_i23 _raw_i24 h_489 h_494 _
        let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_489)
        have h_489 : Litex.In _value_i23 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) := h_489
        have h_490 : Litex.In _value_i23 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i23 h_489).1
              )
          )
        have h_491 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i23 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i23 h_489).2.1
              )
          )
        have h_492 : Litex.Le _value_i23 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i23 h_489).2.2
              )
          )
        have h_493 : Litex.In _value_i23 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i23 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_489)
              )
          )
        let _value_i24 := Litex.semanticObject (M := M) _raw_i24 (M.member_isSet h_494)
        have h_494 : Litex.In _value_i24 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) := h_494
        have h_495 : Litex.In _value_i24 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i24 h_494).1
              )
          )
        have h_496 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i24 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i24 h_494).2.1
              )
          )
        have h_497 : Litex.Le _value_i24 _value_i2 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i24 h_494).2.2
              )
          )
        have h_498 : Litex.In _value_i24 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i24 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_494)
              )
          )
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
    exact (Litex.inOfSame _value_i3 _value_i3 _object_h43 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h43
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_43)) (by
    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i25 : M.Value) (_raw_i26 : M.Value), M.mem _raw_i25 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))) → M.mem _raw_i26 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))) → ((fun (_raw_i25 : M.Value) (_raw_i26 : M.Value) => True) _raw_i25 _raw_i26) → True := (by
        intro _raw_i25 _raw_i26 h_512 h_517 _
        let _value_i25 := Litex.semanticObject (M := M) _raw_i25 (M.member_isSet h_512)
        have h_512 : Litex.In _value_i25 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) := h_512
        have h_513 : Litex.In _value_i25 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i25 h_512).1
              )
          )
        have h_514 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i25 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i25 h_512).2.1
              )
          )
        have h_515 : Litex.Le _value_i25 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i25 h_512).2.2
              )
          )
        have h_516 : Litex.In _value_i25 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i25 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_512)
              )
          )
        let _value_i26 := Litex.semanticObject (M := M) _raw_i26 (M.member_isSet h_517)
        have h_517 : Litex.In _value_i26 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) := h_517
        have h_518 : Litex.In _value_i26 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i26 h_517).1
              )
          )
        have h_519 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i26 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i26 h_517).2.1
              )
          )
        have h_520 : Litex.Le _value_i26 _value_i2 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i26 h_517).2.2
              )
          )
        have h_521 : Litex.In _value_i26 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i26 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_517)
              )
          )
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i25 : M.Value) (_raw_i26 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
    exact (Litex.inOfSame _value_i4 _value_i4 _object_h45 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h45
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_45))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
    exact h_84) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
    exact h_143)), True.intro⟩)))
  exact (by
    let _atomic_wd_1_0 := _object_w11
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_25 _Host_i2 _rep_i2 _value_i2 h_27 _Host_i3 _rep_i3 _value_i3 h_42 _Host_i4 _rep_i4 _value_i4 h_44 _Host_i5 _rep_i5 _value_i5 h_84 _Host_i6 _rep_i6 _value_i6 h_143
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
          let _object_h43 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27)))
          have h_43 : Litex.In _value_i3 _object_h43 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27) _object_h43 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27))) h_42)
                )
            )
          let _object_h45 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27)))
          have h_45 : Litex.In _value_i4 _object_h45 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27) _object_h45 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_25 h_27))) h_44)
                )
            )
          have h_85 : Litex.In _value_i5 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i5 h_84).1
                )
            )
          have h_86 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i5 h_84).2.1
                )
            )
          have h_87 : Litex.Le _value_i5 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i5 h_84).2.2
                )
            )
          have h_88 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_84)
                )
            )
          have h_144 : Litex.In _value_i6 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i6 h_143).1
                )
            )
          have h_145 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i6 h_143).2.1
                )
            )
          have h_146 : Litex.Le _value_i6 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i6 h_143).2.2
                )
            )
          have h_147 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_143)
                )
            )
          let _object_w11 := (let _litex_matrix_head := (Litex.matrixEntrywise .add _value_i3 _value_i4 _value_i1 _value_i2 h_25 h_27 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
            exact (show Litex.In _value_i3 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i15 : M.Value) (_raw_i16 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))) → M.mem _raw_i16 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))) → ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) _raw_i15 _raw_i16) → True := (by
                  intro _raw_i15 _raw_i16 h_300 h_305 _
                  let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_300)
                  have h_300 : Litex.In _value_i15 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) := h_300
                  have h_301 : Litex.In _value_i15 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i15 h_300).1
                        )
                    )
                  have h_302 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i15 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i15 h_300).2.1
                        )
                    )
                  have h_303 : Litex.Le _value_i15 _value_i1 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i15 h_300).2.2
                        )
                    )
                  have h_304 : Litex.In _value_i15 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i15 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_300)
                        )
                    )
                  let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_305)
                  have h_305 : Litex.In _value_i16 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) := h_305
                  have h_306 : Litex.In _value_i16 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i16 h_305).1
                        )
                    )
                  have h_307 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i16 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i16 h_305).2.1
                        )
                    )
                  have h_308 : Litex.Le _value_i16 _value_i2 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i16 h_305).2.2
                        )
                    )
                  have h_309 : Litex.In _value_i16 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i16 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_305)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i3 _value_i3 _object_h43 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h43
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_43))))) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
            exact (show Litex.In _value_i4 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i21 : M.Value) (_raw_i22 : M.Value), M.mem _raw_i21 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))) → M.mem _raw_i22 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))) → ((fun (_raw_i21 : M.Value) (_raw_i22 : M.Value) => True) _raw_i21 _raw_i22) → True := (by
                  intro _raw_i21 _raw_i22 h_462 h_467 _
                  let _value_i21 := Litex.semanticObject (M := M) _raw_i21 (M.member_isSet h_462)
                  have h_462 : Litex.In _value_i21 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) := h_462
                  have h_463 : Litex.In _value_i21 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i21 h_462).1
                        )
                    )
                  have h_464 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i21 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i21 h_462).2.1
                        )
                    )
                  have h_465 : Litex.Le _value_i21 _value_i1 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i21 h_462).2.2
                        )
                    )
                  have h_466 : Litex.In _value_i21 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i21 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_462)
                        )
                    )
                  let _value_i22 := Litex.semanticObject (M := M) _raw_i22 (M.member_isSet h_467)
                  have h_467 : Litex.In _value_i22 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) := h_467
                  have h_468 : Litex.In _value_i22 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i22 h_467).1
                        )
                    )
                  have h_469 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i22 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i22 h_467).2.1
                        )
                    )
                  have h_470 : Litex.Le _value_i22 _value_i2 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i22 h_467).2.2
                        )
                    )
                  have h_471 : Litex.In _value_i22 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i22 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_467)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i21 : M.Value) (_raw_i22 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i4 _value_i4 _object_h45 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h45
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_45))))));
          (let _litex_call_arg_0 := _value_i5;
          let _litex_call_arg_1 := _value_i6;
          Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixEntrywiseInRealFnSet _litex_matrix_head (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i23 : M.Value) (_raw_i24 : M.Value), M.mem _raw_i23 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))) → M.mem _raw_i24 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))) → ((fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) _raw_i23 _raw_i24) → True := (by
                intro _raw_i23 _raw_i24 h_489 h_494 _
                let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_489)
                have h_489 : Litex.In _value_i23 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) := h_489
                have h_490 : Litex.In _value_i23 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i23 h_489).1
                      )
                  )
                have h_491 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i23 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i23 h_489).2.1
                      )
                  )
                have h_492 : Litex.Le _value_i23 _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i23 h_489).2.2
                      )
                  )
                have h_493 : Litex.In _value_i23 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i23 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_489)
                      )
                  )
                let _value_i24 := Litex.semanticObject (M := M) _raw_i24 (M.member_isSet h_494)
                have h_494 : Litex.In _value_i24 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) := h_494
                have h_495 : Litex.In _value_i24 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i24 h_494).1
                      )
                  )
                have h_496 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i24 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i24 h_494).2.1
                      )
                  )
                have h_497 : Litex.Le _value_i24 _value_i2 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i24 h_494).2.2
                      )
                  )
                have h_498 : Litex.In _value_i24 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i24 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_494)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
            exact (Litex.inOfSame _value_i3 _value_i3 _object_h43 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h43
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_43)) (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i25 : M.Value) (_raw_i26 : M.Value), M.mem _raw_i25 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))) → M.mem _raw_i26 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))) → ((fun (_raw_i25 : M.Value) (_raw_i26 : M.Value) => True) _raw_i25 _raw_i26) → True := (by
                intro _raw_i25 _raw_i26 h_512 h_517 _
                let _value_i25 := Litex.semanticObject (M := M) _raw_i25 (M.member_isSet h_512)
                have h_512 : Litex.In _value_i25 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) := h_512
                have h_513 : Litex.In _value_i25 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i25 h_512).1
                      )
                  )
                have h_514 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i25 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i25 h_512).2.1
                      )
                  )
                have h_515 : Litex.Le _value_i25 _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i25 h_512).2.2
                      )
                  )
                have h_516 : Litex.In _value_i25 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i25 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_512)
                      )
                  )
                let _value_i26 := Litex.semanticObject (M := M) _raw_i26 (M.member_isSet h_517)
                have h_517 : Litex.In _value_i26 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) := h_517
                have h_518 : Litex.In _value_i26 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i26 h_517).1
                      )
                  )
                have h_519 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i26 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i26 h_517).2.1
                      )
                  )
                have h_520 : Litex.Le _value_i26 _value_i2 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i26 h_517).2.2
                      )
                  )
                have h_521 : Litex.In _value_i26 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i26 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_517)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i25 : M.Value) (_raw_i26 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
            exact (Litex.inOfSame _value_i4 _value_i4 _object_h45 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h45
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_45))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
            exact h_84) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
            exact h_143)), True.intro⟩)))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w11
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w11
                    exact (show Litex.In _atomic_wd_1_0 (Litex.R (M := M)) from (let _litex_matrix_signature := (Litex.matrixEntrywiseSignature ((_atomic_wd_1_0).val.function).val.rows ((_atomic_wd_1_0).val.function).val.cols .real); Litex.FunctionSemantics.call_mem _litex_matrix_signature.domain _litex_matrix_signature.output (Litex.denote (_atomic_wd_1_0).val.function) (Litex.denote (Litex.callArguments2 _value_i5 _value_i6)) (let _litex_matrix := (_atomic_wd_1_0).val.function; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixEntrywiseInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i29 : M.Value) (_raw_i30 : M.Value), M.mem _raw_i29 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))) → M.mem _raw_i30 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))) → ((fun (_raw_i29 : M.Value) (_raw_i30 : M.Value) => True) _raw_i29 _raw_i30) → True := (by
                          intro _raw_i29 _raw_i30 h_808 h_813 _
                          let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_808)
                          have h_808 : Litex.In _value_i29 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) := h_808
                          have h_809 : Litex.In _value_i29 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i29 h_808).1
                                )
                            )
                          have h_810 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i29 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i29 h_808).2.1
                                )
                            )
                          have h_811 : Litex.Le _value_i29 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i29 h_808).2.2
                                )
                            )
                          have h_812 : Litex.In _value_i29 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i29 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_808)
                                )
                            )
                          let _value_i30 := Litex.semanticObject (M := M) _raw_i30 (M.member_isSet h_813)
                          have h_813 : Litex.In _value_i30 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) := h_813
                          have h_814 : Litex.In _value_i30 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i30 h_813).1
                                )
                            )
                          have h_815 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i30 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i30 h_813).2.1
                                )
                            )
                          have h_816 : Litex.Le _value_i30 _value_i2 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i30 h_813).2.2
                                )
                            )
                          have h_817 : Litex.In _value_i30 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i30 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_813)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i29 : M.Value) (_raw_i30 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i3 _value_i3 _object_h43 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h43
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_43)) (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i31 : M.Value) (_raw_i32 : M.Value), M.mem _raw_i31 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))) → M.mem _raw_i32 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))) → ((fun (_raw_i31 : M.Value) (_raw_i32 : M.Value) => True) _raw_i31 _raw_i32) → True := (by
                          intro _raw_i31 _raw_i32 h_831 h_836 _
                          let _value_i31 := Litex.semanticObject (M := M) _raw_i31 (M.member_isSet h_831)
                          have h_831 : Litex.In _value_i31 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) := h_831
                          have h_832 : Litex.In _value_i31 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i31 h_831).1
                                )
                            )
                          have h_833 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i31 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i31 h_831).2.1
                                )
                            )
                          have h_834 : Litex.Le _value_i31 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i31 h_831).2.2
                                )
                            )
                          have h_835 : Litex.In _value_i31 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)) _value_i31 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_831)
                                )
                            )
                          let _value_i32 := Litex.semanticObject (M := M) _raw_i32 (M.member_isSet h_836)
                          have h_836 : Litex.In _value_i32 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) := h_836
                          have h_837 : Litex.In _value_i32 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i32 h_836).1
                                )
                            )
                          have h_838 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i32 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i32 h_836).2.1
                                )
                            )
                          have h_839 : Litex.Le _value_i32 _value_i2 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i32 h_836).2.2
                                )
                            )
                          have h_840 : Litex.In _value_i32 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)) _value_i32 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_836)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i31 : M.Value) (_raw_i32 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i4 _value_i4 _object_h45 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h45
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_45)))) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))) (fun (_litex_input : M.Value) => (fun (_raw_i33 : M.Value) (_raw_i34 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i5 _value_i6))).mpr ⟨(Litex.callArguments2_mem_cart _value_i5 _value_i6 (by
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_25))
                      exact h_84) (by
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_27))
                      exact h_143)), True.intro⟩))))
                )
            )
          exact h_1
        )
      )
  )

theorem h_858 : ∀ {_Host_i35 : Type v35} [_rep_i35 : Litex.Representation M _Host_i35] (_value_i35 : Litex.Obj (M := M) _Host_i35) (h_882 : Litex.In _value_i35 (Litex.N (M := M))) {_Host_i36 : Type v36} [_rep_i36 : Litex.Representation M _Host_i36] (_value_i36 : Litex.Obj (M := M) _Host_i36) (h_884 : Litex.In _value_i36 (Litex.N (M := M))) {_Host_i37 : Type v37} [_rep_i37 : Litex.Representation M _Host_i37] (_value_i37 : Litex.Obj (M := M) _Host_i37) (h_899 : Litex.In _value_i37 (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884)) {_Host_i38 : Type v38} [_rep_i38 : Litex.Representation M _Host_i38] (_value_i38 : Litex.Obj (M := M) _Host_i38) (h_901 : Litex.In _value_i38 (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884)) {_Host_i39 : Type v39} [_rep_i39 : Litex.Representation M _Host_i39] (_value_i39 : Litex.Obj (M := M) _Host_i39) (h_941 : Litex.In _value_i39 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))) {_Host_i40 : Type v40} [_rep_i40 : Litex.Representation M _Host_i40] (_value_i40 : Litex.Obj (M := M) _Host_i40) (h_1000 : Litex.In _value_i40 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))), (by
  let _object_h900 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884)))
  have h_900 : Litex.In _value_i37 _object_h900 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i37 _value_i37 (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884) _object_h900 (Litex.sameRefl _value_i37) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884))) h_899)
        )
    )
  let _object_h902 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884)))
  have h_902 : Litex.In _value_i38 _object_h902 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i38 _value_i38 (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884) _object_h902 (Litex.sameRefl _value_i38) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884))) h_901)
        )
    )
  let _object_w23 := (let _litex_matrix_head := (Litex.matrixEntrywise .sub _value_i37 _value_i38 _value_i35 _value_i36 h_882 h_884 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.C (M := M))) h_882 h_884)
    exact (show Litex.In _value_i37 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i49 : M.Value) (_raw_i50 : M.Value), M.mem _raw_i49 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))) → M.mem _raw_i50 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))) → ((fun (_raw_i49 : M.Value) (_raw_i50 : M.Value) => True) _raw_i49 _raw_i50) → True := (by
          intro _raw_i49 _raw_i50 h_1157 h_1162 _
          let _value_i49 := Litex.semanticObject (M := M) _raw_i49 (M.member_isSet h_1157)
          have h_1157 : Litex.In _value_i49 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) := h_1157
          have h_1158 : Litex.In _value_i49 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i49 h_1157).1
                )
            )
          have h_1159 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i49 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i49 h_1157).2.1
                )
            )
          have h_1160 : Litex.Le _value_i49 _value_i35 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i49 h_1157).2.2
                )
            )
          have h_1161 : Litex.In _value_i49 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i49 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1157)
                )
            )
          let _value_i50 := Litex.semanticObject (M := M) _raw_i50 (M.member_isSet h_1162)
          have h_1162 : Litex.In _value_i50 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) := h_1162
          have h_1163 : Litex.In _value_i50 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i50 h_1162).1
                )
            )
          have h_1164 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i50 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i50 h_1162).2.1
                )
            )
          have h_1165 : Litex.Le _value_i50 _value_i36 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i50 h_1162).2.2
                )
            )
          have h_1166 : Litex.In _value_i50 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i50 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1162)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i49 : M.Value) (_raw_i50 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i37 _value_i37 _object_h900 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h900
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_900))))) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.C (M := M))) h_882 h_884)
    exact (show Litex.In _value_i38 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i55 : M.Value) (_raw_i56 : M.Value), M.mem _raw_i55 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))) → M.mem _raw_i56 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))) → ((fun (_raw_i55 : M.Value) (_raw_i56 : M.Value) => True) _raw_i55 _raw_i56) → True := (by
          intro _raw_i55 _raw_i56 h_1319 h_1324 _
          let _value_i55 := Litex.semanticObject (M := M) _raw_i55 (M.member_isSet h_1319)
          have h_1319 : Litex.In _value_i55 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) := h_1319
          have h_1320 : Litex.In _value_i55 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i55 h_1319).1
                )
            )
          have h_1321 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i55 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i55 h_1319).2.1
                )
            )
          have h_1322 : Litex.Le _value_i55 _value_i35 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i55 h_1319).2.2
                )
            )
          have h_1323 : Litex.In _value_i55 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i55 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1319)
                )
            )
          let _value_i56 := Litex.semanticObject (M := M) _raw_i56 (M.member_isSet h_1324)
          have h_1324 : Litex.In _value_i56 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) := h_1324
          have h_1325 : Litex.In _value_i56 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i56 h_1324).1
                )
            )
          have h_1326 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i56 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i56 h_1324).2.1
                )
            )
          have h_1327 : Litex.Le _value_i56 _value_i36 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i56 h_1324).2.2
                )
            )
          have h_1328 : Litex.In _value_i56 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i56 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1324)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i55 : M.Value) (_raw_i56 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i38 _value_i38 _object_h902 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h902
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_902))))));
  (let _litex_call_arg_0 := _value_i39;
  let _litex_call_arg_1 := _value_i40;
  Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixEntrywiseInRealFnSet _litex_matrix_head (by
    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i57 : M.Value) (_raw_i58 : M.Value), M.mem _raw_i57 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))) → M.mem _raw_i58 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))) → ((fun (_raw_i57 : M.Value) (_raw_i58 : M.Value) => True) _raw_i57 _raw_i58) → True := (by
        intro _raw_i57 _raw_i58 h_1346 h_1351 _
        let _value_i57 := Litex.semanticObject (M := M) _raw_i57 (M.member_isSet h_1346)
        have h_1346 : Litex.In _value_i57 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) := h_1346
        have h_1347 : Litex.In _value_i57 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i57 h_1346).1
              )
          )
        have h_1348 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i57 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i57 h_1346).2.1
              )
          )
        have h_1349 : Litex.Le _value_i57 _value_i35 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i57 h_1346).2.2
              )
          )
        have h_1350 : Litex.In _value_i57 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i57 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1346)
              )
          )
        let _value_i58 := Litex.semanticObject (M := M) _raw_i58 (M.member_isSet h_1351)
        have h_1351 : Litex.In _value_i58 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) := h_1351
        have h_1352 : Litex.In _value_i58 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i58 h_1351).1
              )
          )
        have h_1353 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i58 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i58 h_1351).2.1
              )
          )
        have h_1354 : Litex.Le _value_i58 _value_i36 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i58 h_1351).2.2
              )
          )
        have h_1355 : Litex.In _value_i58 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i58 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1351)
              )
          )
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)))
      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i57 : M.Value) (_raw_i58 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
    exact (Litex.inOfSame _value_i37 _value_i37 _object_h900 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h900
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_900)) (by
    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i59 : M.Value) (_raw_i60 : M.Value), M.mem _raw_i59 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))) → M.mem _raw_i60 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))) → ((fun (_raw_i59 : M.Value) (_raw_i60 : M.Value) => True) _raw_i59 _raw_i60) → True := (by
        intro _raw_i59 _raw_i60 h_1369 h_1374 _
        let _value_i59 := Litex.semanticObject (M := M) _raw_i59 (M.member_isSet h_1369)
        have h_1369 : Litex.In _value_i59 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) := h_1369
        have h_1370 : Litex.In _value_i59 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i59 h_1369).1
              )
          )
        have h_1371 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i59 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i59 h_1369).2.1
              )
          )
        have h_1372 : Litex.Le _value_i59 _value_i35 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i59 h_1369).2.2
              )
          )
        have h_1373 : Litex.In _value_i59 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i59 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1369)
              )
          )
        let _value_i60 := Litex.semanticObject (M := M) _raw_i60 (M.member_isSet h_1374)
        have h_1374 : Litex.In _value_i60 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) := h_1374
        have h_1375 : Litex.In _value_i60 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i60 h_1374).1
              )
          )
        have h_1376 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i60 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i60 h_1374).2.1
              )
          )
        have h_1377 : Litex.Le _value_i60 _value_i36 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i60 h_1374).2.2
              )
          )
        have h_1378 : Litex.In _value_i60 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i60 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1374)
              )
          )
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)))
      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i59 : M.Value) (_raw_i60 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
    exact (Litex.inOfSame _value_i38 _value_i38 _object_h902 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h902
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_902))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))
    exact h_941) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))
    exact h_1000)), True.intro⟩)))
  exact (by
    let _atomic_wd_1_0 := _object_w23
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i35 _rep_i35 _value_i35 h_882 _Host_i36 _rep_i36 _value_i36 h_884 _Host_i37 _rep_i37 _value_i37 h_899 _Host_i38 _rep_i38 _value_i38 h_901 _Host_i39 _rep_i39 _value_i39 h_941 _Host_i40 _rep_i40 _value_i40 h_1000
          have h_883 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i35 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i35 h_882)
                )
            )
          have h_885 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i36 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i36 h_884)
                )
            )
          let _object_h900 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884)))
          have h_900 : Litex.In _value_i37 _object_h900 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i37 _value_i37 (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884) _object_h900 (Litex.sameRefl _value_i37) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884))) h_899)
                )
            )
          let _object_h902 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884)))
          have h_902 : Litex.In _value_i38 _object_h902 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i38 _value_i38 (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884) _object_h902 (Litex.sameRefl _value_i38) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.R (M := M))) h_882 h_884))) h_901)
                )
            )
          have h_942 : Litex.In _value_i39 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i39 h_941).1
                )
            )
          have h_943 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i39 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i39 h_941).2.1
                )
            )
          have h_944 : Litex.Le _value_i39 _value_i35 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i39 h_941).2.2
                )
            )
          have h_945 : Litex.In _value_i39 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i39 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_941)
                )
            )
          have h_1001 : Litex.In _value_i40 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i40 h_1000).1
                )
            )
          have h_1002 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i40 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i40 h_1000).2.1
                )
            )
          have h_1003 : Litex.Le _value_i40 _value_i36 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i40 h_1000).2.2
                )
            )
          have h_1004 : Litex.In _value_i40 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i40 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1000)
                )
            )
          let _object_w23 := (let _litex_matrix_head := (Litex.matrixEntrywise .sub _value_i37 _value_i38 _value_i35 _value_i36 h_882 h_884 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.C (M := M))) h_882 h_884)
            exact (show Litex.In _value_i37 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i49 : M.Value) (_raw_i50 : M.Value), M.mem _raw_i49 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))) → M.mem _raw_i50 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))) → ((fun (_raw_i49 : M.Value) (_raw_i50 : M.Value) => True) _raw_i49 _raw_i50) → True := (by
                  intro _raw_i49 _raw_i50 h_1157 h_1162 _
                  let _value_i49 := Litex.semanticObject (M := M) _raw_i49 (M.member_isSet h_1157)
                  have h_1157 : Litex.In _value_i49 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) := h_1157
                  have h_1158 : Litex.In _value_i49 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i49 h_1157).1
                        )
                    )
                  have h_1159 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i49 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i49 h_1157).2.1
                        )
                    )
                  have h_1160 : Litex.Le _value_i49 _value_i35 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i49 h_1157).2.2
                        )
                    )
                  have h_1161 : Litex.In _value_i49 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i49 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1157)
                        )
                    )
                  let _value_i50 := Litex.semanticObject (M := M) _raw_i50 (M.member_isSet h_1162)
                  have h_1162 : Litex.In _value_i50 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) := h_1162
                  have h_1163 : Litex.In _value_i50 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i50 h_1162).1
                        )
                    )
                  have h_1164 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i50 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i50 h_1162).2.1
                        )
                    )
                  have h_1165 : Litex.Le _value_i50 _value_i36 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i50 h_1162).2.2
                        )
                    )
                  have h_1166 : Litex.In _value_i50 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i50 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1162)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i49 : M.Value) (_raw_i50 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i37 _value_i37 _object_h900 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h900
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_900))))) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i35 _value_i36 (Litex.isSet (Litex.C (M := M))) h_882 h_884)
            exact (show Litex.In _value_i38 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i55 : M.Value) (_raw_i56 : M.Value), M.mem _raw_i55 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))) → M.mem _raw_i56 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))) → ((fun (_raw_i55 : M.Value) (_raw_i56 : M.Value) => True) _raw_i55 _raw_i56) → True := (by
                  intro _raw_i55 _raw_i56 h_1319 h_1324 _
                  let _value_i55 := Litex.semanticObject (M := M) _raw_i55 (M.member_isSet h_1319)
                  have h_1319 : Litex.In _value_i55 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) := h_1319
                  have h_1320 : Litex.In _value_i55 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i55 h_1319).1
                        )
                    )
                  have h_1321 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i55 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i55 h_1319).2.1
                        )
                    )
                  have h_1322 : Litex.Le _value_i55 _value_i35 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i55 h_1319).2.2
                        )
                    )
                  have h_1323 : Litex.In _value_i55 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i55 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1319)
                        )
                    )
                  let _value_i56 := Litex.semanticObject (M := M) _raw_i56 (M.member_isSet h_1324)
                  have h_1324 : Litex.In _value_i56 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) := h_1324
                  have h_1325 : Litex.In _value_i56 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i56 h_1324).1
                        )
                    )
                  have h_1326 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i56 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i56 h_1324).2.1
                        )
                    )
                  have h_1327 : Litex.Le _value_i56 _value_i36 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i56 h_1324).2.2
                        )
                    )
                  have h_1328 : Litex.In _value_i56 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i56 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1324)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i55 : M.Value) (_raw_i56 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i38 _value_i38 _object_h902 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h902
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_902))))));
          (let _litex_call_arg_0 := _value_i39;
          let _litex_call_arg_1 := _value_i40;
          Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixEntrywiseInRealFnSet _litex_matrix_head (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i57 : M.Value) (_raw_i58 : M.Value), M.mem _raw_i57 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))) → M.mem _raw_i58 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))) → ((fun (_raw_i57 : M.Value) (_raw_i58 : M.Value) => True) _raw_i57 _raw_i58) → True := (by
                intro _raw_i57 _raw_i58 h_1346 h_1351 _
                let _value_i57 := Litex.semanticObject (M := M) _raw_i57 (M.member_isSet h_1346)
                have h_1346 : Litex.In _value_i57 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) := h_1346
                have h_1347 : Litex.In _value_i57 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i57 h_1346).1
                      )
                  )
                have h_1348 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i57 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i57 h_1346).2.1
                      )
                  )
                have h_1349 : Litex.Le _value_i57 _value_i35 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i57 h_1346).2.2
                      )
                  )
                have h_1350 : Litex.In _value_i57 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i57 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1346)
                      )
                  )
                let _value_i58 := Litex.semanticObject (M := M) _raw_i58 (M.member_isSet h_1351)
                have h_1351 : Litex.In _value_i58 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) := h_1351
                have h_1352 : Litex.In _value_i58 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i58 h_1351).1
                      )
                  )
                have h_1353 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i58 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i58 h_1351).2.1
                      )
                  )
                have h_1354 : Litex.Le _value_i58 _value_i36 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i58 h_1351).2.2
                      )
                  )
                have h_1355 : Litex.In _value_i58 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i58 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1351)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))] (by
              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)))
              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i57 : M.Value) (_raw_i58 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
            exact (Litex.inOfSame _value_i37 _value_i37 _object_h900 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h900
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_900)) (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i59 : M.Value) (_raw_i60 : M.Value), M.mem _raw_i59 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))) → M.mem _raw_i60 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))) → ((fun (_raw_i59 : M.Value) (_raw_i60 : M.Value) => True) _raw_i59 _raw_i60) → True := (by
                intro _raw_i59 _raw_i60 h_1369 h_1374 _
                let _value_i59 := Litex.semanticObject (M := M) _raw_i59 (M.member_isSet h_1369)
                have h_1369 : Litex.In _value_i59 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) := h_1369
                have h_1370 : Litex.In _value_i59 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i59 h_1369).1
                      )
                  )
                have h_1371 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i59 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i59 h_1369).2.1
                      )
                  )
                have h_1372 : Litex.Le _value_i59 _value_i35 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i59 h_1369).2.2
                      )
                  )
                have h_1373 : Litex.In _value_i59 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i59 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1369)
                      )
                  )
                let _value_i60 := Litex.semanticObject (M := M) _raw_i60 (M.member_isSet h_1374)
                have h_1374 : Litex.In _value_i60 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) := h_1374
                have h_1375 : Litex.In _value_i60 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i60 h_1374).1
                      )
                  )
                have h_1376 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i60 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i60 h_1374).2.1
                      )
                  )
                have h_1377 : Litex.Le _value_i60 _value_i36 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i60 h_1374).2.2
                      )
                  )
                have h_1378 : Litex.In _value_i60 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i60 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1374)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))] (by
              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)))
              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i59 : M.Value) (_raw_i60 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
            exact (Litex.inOfSame _value_i38 _value_i38 _object_h902 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h902
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_902))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))
            exact h_941) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))
            exact h_1000)), True.intro⟩)))
          have h_857 : (by
            let _atomic_wd_1_0 := _object_w23
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w23
                    exact (show Litex.In _atomic_wd_1_0 (Litex.R (M := M)) from (let _litex_matrix_signature := (Litex.matrixEntrywiseSignature ((_atomic_wd_1_0).val.function).val.rows ((_atomic_wd_1_0).val.function).val.cols .real); Litex.FunctionSemantics.call_mem _litex_matrix_signature.domain _litex_matrix_signature.output (Litex.denote (_atomic_wd_1_0).val.function) (Litex.denote (Litex.callArguments2 _value_i39 _value_i40)) (let _litex_matrix := (_atomic_wd_1_0).val.function; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixEntrywiseInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i63 : M.Value) (_raw_i64 : M.Value), M.mem _raw_i63 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))) → M.mem _raw_i64 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))) → ((fun (_raw_i63 : M.Value) (_raw_i64 : M.Value) => True) _raw_i63 _raw_i64) → True := (by
                          intro _raw_i63 _raw_i64 h_1665 h_1670 _
                          let _value_i63 := Litex.semanticObject (M := M) _raw_i63 (M.member_isSet h_1665)
                          have h_1665 : Litex.In _value_i63 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) := h_1665
                          have h_1666 : Litex.In _value_i63 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i63 h_1665).1
                                )
                            )
                          have h_1667 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i63 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i63 h_1665).2.1
                                )
                            )
                          have h_1668 : Litex.Le _value_i63 _value_i35 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i63 h_1665).2.2
                                )
                            )
                          have h_1669 : Litex.In _value_i63 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i63 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1665)
                                )
                            )
                          let _value_i64 := Litex.semanticObject (M := M) _raw_i64 (M.member_isSet h_1670)
                          have h_1670 : Litex.In _value_i64 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) := h_1670
                          have h_1671 : Litex.In _value_i64 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i64 h_1670).1
                                )
                            )
                          have h_1672 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i64 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i64 h_1670).2.1
                                )
                            )
                          have h_1673 : Litex.Le _value_i64 _value_i36 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i64 h_1670).2.2
                                )
                            )
                          have h_1674 : Litex.In _value_i64 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i64 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1670)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i63 : M.Value) (_raw_i64 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i37 _value_i37 _object_h900 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h900
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_900)) (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i65 : M.Value) (_raw_i66 : M.Value), M.mem _raw_i65 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))) → M.mem _raw_i66 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))) → ((fun (_raw_i65 : M.Value) (_raw_i66 : M.Value) => True) _raw_i65 _raw_i66) → True := (by
                          intro _raw_i65 _raw_i66 h_1688 h_1693 _
                          let _value_i65 := Litex.semanticObject (M := M) _raw_i65 (M.member_isSet h_1688)
                          have h_1688 : Litex.In _value_i65 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) := h_1688
                          have h_1689 : Litex.In _value_i65 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i65 h_1688).1
                                )
                            )
                          have h_1690 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i65 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i65 h_1688).2.1
                                )
                            )
                          have h_1691 : Litex.Le _value_i65 _value_i35 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i65 h_1688).2.2
                                )
                            )
                          have h_1692 : Litex.In _value_i65 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)) _value_i65 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1688)
                                )
                            )
                          let _value_i66 := Litex.semanticObject (M := M) _raw_i66 (M.member_isSet h_1693)
                          have h_1693 : Litex.In _value_i66 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) := h_1693
                          have h_1694 : Litex.In _value_i66 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i66 h_1693).1
                                )
                            )
                          have h_1695 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i66 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i66 h_1693).2.1
                                )
                            )
                          have h_1696 : Litex.Le _value_i66 _value_i36 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i66 h_1693).2.2
                                )
                            )
                          have h_1697 : Litex.In _value_i66 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)) _value_i66 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1693)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i65 : M.Value) (_raw_i66 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i38 _value_i38 _object_h902 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h902
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_902)))) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))) (fun (_litex_input : M.Value) => (fun (_raw_i67 : M.Value) (_raw_i68 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i39 _value_i40))).mpr ⟨(Litex.callArguments2_mem_cart _value_i39 _value_i40 (by
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i35 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i35 h_882))
                      exact h_941) (by
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i36 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i36 h_884))
                      exact h_1000)), True.intro⟩))))
                )
            )
          exact h_857
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_entrywise_x5f_real_x2f_statement_x2e_lit
