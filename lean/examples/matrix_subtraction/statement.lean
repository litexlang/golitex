import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_subtraction_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v19 v20 v21 v22
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_21 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_36 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_38 : Litex.In _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)), (by
  let _object_w11 := (Litex.matrixEntrywise .sub _value_i3 _value_i4 _value_i1 _value_i2 h_19 h_21 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
    exact h_36) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
    exact h_38))
  exact (by
    let _atomic_wd_1_0 := _object_w11
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_19 _Host_i2 _rep_i2 _value_i2 h_21 _Host_i3 _rep_i3 _value_i3 h_36 _Host_i4 _rep_i4 _value_i4 h_38
          have h_20 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_19)
                )
            )
          have h_22 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_21)
                )
            )
          let _object_h37 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)))
          have h_37 : Litex.In _value_i3 _object_h37 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21) _object_h37 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21))) h_36)
                )
            )
          let _object_h39 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)))
          have h_39 : Litex.In _value_i4 _object_h39 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21) _object_h39 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21))) h_38)
                )
            )
          let _object_w11 := (Litex.matrixEntrywise .sub _value_i3 _value_i4 _value_i1 _value_i2 h_19 h_21 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
            exact h_36) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
            exact h_38))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w11
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w11
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixEntrywiseInFnSet _litex_matrix))))
                )
            )
          let _object_h219 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)))
          have h_219 : Litex.In _object_w11 _object_h219 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w11 _object_w11 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21) _object_h219 (Litex.sameRefl _object_w11) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21))) h_1)
                )
            )
          exact h_1
        )
      )
  )

theorem h_221 : ∀ {_Host_i19 : Type v19} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_238 : Litex.In _value_i19 (Litex.N (M := M))) {_Host_i20 : Type v20} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (h_240 : Litex.In _value_i20 (Litex.N (M := M))) {_Host_i21 : Type v21} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (h_255 : Litex.In _value_i21 (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240)) {_Host_i22 : Type v22} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (h_257 : Litex.In _value_i22 (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240)), (by
  let _object_h256 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240)))
  have h_256 : Litex.In _value_i21 _object_h256 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i21 _value_i21 (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240) _object_h256 (Litex.sameRefl _value_i21) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240))) h_255)
        )
    )
  let _object_h258 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240)))
  have h_258 : Litex.In _value_i22 _object_h258 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i22 _value_i22 (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240) _object_h258 (Litex.sameRefl _value_i22) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240))) h_257)
        )
    )
  let _object_w48 := (Litex.matrixEntrywise .sub _value_i21 _value_i22 _value_i19 _value_i20 h_238 h_240 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.C (M := M))) h_238 h_240)
    exact (show Litex.In _value_i21 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i31 : M.Value) (_raw_i32 : M.Value), M.mem _raw_i31 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))) → M.mem _raw_i32 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240))) → ((fun (_raw_i31 : M.Value) (_raw_i32 : M.Value) => True) _raw_i31 _raw_i32) → True := (by
          intro _raw_i31 _raw_i32 h_517 h_522 _
          let _value_i31 := Litex.semanticObject (M := M) _raw_i31 (M.member_isSet h_517)
          have h_517 : Litex.In _value_i31 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) := h_517
          have h_518 : Litex.In _value_i31 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i31 h_517).1
                )
            )
          have h_519 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i31 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i31 h_517).2.1
                )
            )
          have h_520 : Litex.Le _value_i31 _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i31 h_517).2.2
                )
            )
          have h_521 : Litex.In _value_i31 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i31 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_517)
                )
            )
          let _value_i32 := Litex.semanticObject (M := M) _raw_i32 (M.member_isSet h_522)
          have h_522 : Litex.In _value_i32 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) := h_522
          have h_523 : Litex.In _value_i32 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i32 h_522).1
                )
            )
          have h_524 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i32 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i32 h_522).2.1
                )
            )
          have h_525 : Litex.Le _value_i32 _value_i20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i32 h_522).2.2
                )
            )
          have h_526 : Litex.In _value_i32 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i32 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_522)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i31 : M.Value) (_raw_i32 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i21 _value_i21 _object_h256 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h256
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_256))))) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.C (M := M))) h_238 h_240)
    exact (show Litex.In _value_i22 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i37 : M.Value) (_raw_i38 : M.Value), M.mem _raw_i37 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))) → M.mem _raw_i38 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240))) → ((fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => True) _raw_i37 _raw_i38) → True := (by
          intro _raw_i37 _raw_i38 h_785 h_790 _
          let _value_i37 := Litex.semanticObject (M := M) _raw_i37 (M.member_isSet h_785)
          have h_785 : Litex.In _value_i37 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) := h_785
          have h_786 : Litex.In _value_i37 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i37 h_785).1
                )
            )
          have h_787 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i37 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i37 h_785).2.1
                )
            )
          have h_788 : Litex.Le _value_i37 _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i37 h_785).2.2
                )
            )
          have h_789 : Litex.In _value_i37 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i37 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_785)
                )
            )
          let _value_i38 := Litex.semanticObject (M := M) _raw_i38 (M.member_isSet h_790)
          have h_790 : Litex.In _value_i38 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) := h_790
          have h_791 : Litex.In _value_i38 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i38 h_790).1
                )
            )
          have h_792 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i38 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i38 h_790).2.1
                )
            )
          have h_793 : Litex.Le _value_i38 _value_i20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i38 h_790).2.2
                )
            )
          have h_794 : Litex.In _value_i38 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i38 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_790)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i22 _value_i22 _object_h258 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h258
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_258))))))
  exact (by
    let _atomic_wd_1_0 := _object_w48
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i19 _rep_i19 _value_i19 h_238 _Host_i20 _rep_i20 _value_i20 h_240 _Host_i21 _rep_i21 _value_i21 h_255 _Host_i22 _rep_i22 _value_i22 h_257
          have h_239 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i19 h_238)
                )
            )
          have h_241 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i20 h_240)
                )
            )
          let _object_h256 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240)))
          have h_256 : Litex.In _value_i21 _object_h256 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i21 _value_i21 (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240) _object_h256 (Litex.sameRefl _value_i21) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240))) h_255)
                )
            )
          let _object_h258 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240)))
          have h_258 : Litex.In _value_i22 _object_h258 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i22 _value_i22 (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240) _object_h258 (Litex.sameRefl _value_i22) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240))) h_257)
                )
            )
          let _object_w48 := (Litex.matrixEntrywise .sub _value_i21 _value_i22 _value_i19 _value_i20 h_238 h_240 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.C (M := M))) h_238 h_240)
            exact (show Litex.In _value_i21 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i31 : M.Value) (_raw_i32 : M.Value), M.mem _raw_i31 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))) → M.mem _raw_i32 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240))) → ((fun (_raw_i31 : M.Value) (_raw_i32 : M.Value) => True) _raw_i31 _raw_i32) → True := (by
                  intro _raw_i31 _raw_i32 h_517 h_522 _
                  let _value_i31 := Litex.semanticObject (M := M) _raw_i31 (M.member_isSet h_517)
                  have h_517 : Litex.In _value_i31 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) := h_517
                  have h_518 : Litex.In _value_i31 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i31 h_517).1
                        )
                    )
                  have h_519 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i31 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i31 h_517).2.1
                        )
                    )
                  have h_520 : Litex.Le _value_i31 _value_i19 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i31 h_517).2.2
                        )
                    )
                  have h_521 : Litex.In _value_i31 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i31 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_517)
                        )
                    )
                  let _value_i32 := Litex.semanticObject (M := M) _raw_i32 (M.member_isSet h_522)
                  have h_522 : Litex.In _value_i32 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) := h_522
                  have h_523 : Litex.In _value_i32 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i32 h_522).1
                        )
                    )
                  have h_524 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i32 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i32 h_522).2.1
                        )
                    )
                  have h_525 : Litex.Le _value_i32 _value_i20 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i32 h_522).2.2
                        )
                    )
                  have h_526 : Litex.In _value_i32 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i32 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_522)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i31 : M.Value) (_raw_i32 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i21 _value_i21 _object_h256 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h256
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_256))))) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.C (M := M))) h_238 h_240)
            exact (show Litex.In _value_i22 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i37 : M.Value) (_raw_i38 : M.Value), M.mem _raw_i37 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))) → M.mem _raw_i38 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240))) → ((fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => True) _raw_i37 _raw_i38) → True := (by
                  intro _raw_i37 _raw_i38 h_785 h_790 _
                  let _value_i37 := Litex.semanticObject (M := M) _raw_i37 (M.member_isSet h_785)
                  have h_785 : Litex.In _value_i37 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) := h_785
                  have h_786 : Litex.In _value_i37 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i37 h_785).1
                        )
                    )
                  have h_787 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i37 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i37 h_785).2.1
                        )
                    )
                  have h_788 : Litex.Le _value_i37 _value_i19 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i37 h_785).2.2
                        )
                    )
                  have h_789 : Litex.In _value_i37 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i37 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_785)
                        )
                    )
                  let _value_i38 := Litex.semanticObject (M := M) _raw_i38 (M.member_isSet h_790)
                  have h_790 : Litex.In _value_i38 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) := h_790
                  have h_791 : Litex.In _value_i38 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i38 h_790).1
                        )
                    )
                  have h_792 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i38 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i38 h_790).2.1
                        )
                    )
                  have h_793 : Litex.Le _value_i38 _value_i20 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i38 h_790).2.2
                        )
                    )
                  have h_794 : Litex.In _value_i38 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i38 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_790)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i37 : M.Value) (_raw_i38 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i22 _value_i22 _object_h258 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h258
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_258))))))
          have h_220 : (by
            let _atomic_wd_1_0 := _object_w48
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w48
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixEntrywiseInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i43 : M.Value) (_raw_i44 : M.Value), M.mem _raw_i43 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))) → M.mem _raw_i44 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240))) → ((fun (_raw_i43 : M.Value) (_raw_i44 : M.Value) => True) _raw_i43 _raw_i44) → True := (by
                          intro _raw_i43 _raw_i44 h_913 h_918 _
                          let _value_i43 := Litex.semanticObject (M := M) _raw_i43 (M.member_isSet h_913)
                          have h_913 : Litex.In _value_i43 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) := h_913
                          have h_914 : Litex.In _value_i43 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i43 h_913).1
                                )
                            )
                          have h_915 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i43 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i43 h_913).2.1
                                )
                            )
                          have h_916 : Litex.Le _value_i43 _value_i19 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i43 h_913).2.2
                                )
                            )
                          have h_917 : Litex.In _value_i43 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i43 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_913)
                                )
                            )
                          let _value_i44 := Litex.semanticObject (M := M) _raw_i44 (M.member_isSet h_918)
                          have h_918 : Litex.In _value_i44 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) := h_918
                          have h_919 : Litex.In _value_i44 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i44 h_918).1
                                )
                            )
                          have h_920 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i44 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i44 h_918).2.1
                                )
                            )
                          have h_921 : Litex.Le _value_i44 _value_i20 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i44 h_918).2.2
                                )
                            )
                          have h_922 : Litex.In _value_i44 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i44 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_918)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i43 : M.Value) (_raw_i44 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i21 _value_i21 _object_h256 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h256
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_256)) (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i45 : M.Value) (_raw_i46 : M.Value), M.mem _raw_i45 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))) → M.mem _raw_i46 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240))) → ((fun (_raw_i45 : M.Value) (_raw_i46 : M.Value) => True) _raw_i45 _raw_i46) → True := (by
                          intro _raw_i45 _raw_i46 h_1013 h_1018 _
                          let _value_i45 := Litex.semanticObject (M := M) _raw_i45 (M.member_isSet h_1013)
                          have h_1013 : Litex.In _value_i45 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) := h_1013
                          have h_1014 : Litex.In _value_i45 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i45 h_1013).1
                                )
                            )
                          have h_1015 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i45 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i45 h_1013).2.1
                                )
                            )
                          have h_1016 : Litex.Le _value_i45 _value_i19 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i45 h_1013).2.2
                                )
                            )
                          have h_1017 : Litex.In _value_i45 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)) _value_i45 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1013)
                                )
                            )
                          let _value_i46 := Litex.semanticObject (M := M) _raw_i46 (M.member_isSet h_1018)
                          have h_1018 : Litex.In _value_i46 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) := h_1018
                          have h_1019 : Litex.In _value_i46 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i46 h_1018).1
                                )
                            )
                          have h_1020 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i46 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i46 h_1018).2.1
                                )
                            )
                          have h_1021 : Litex.Le _value_i46 _value_i20 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i46 h_1018).2.2
                                )
                            )
                          have h_1022 : Litex.In _value_i46 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)) _value_i46 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1018)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_238)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i20 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i20 h_240)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i45 : M.Value) (_raw_i46 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i22 _value_i22 _object_h258 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h258
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_258))))))
                )
            )
          let _object_h1039 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240)))
          have h_1039 : Litex.In _object_w48 _object_h1039 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w48 _object_w48 (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240) _object_h1039 (Litex.sameRefl _object_w48) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i20 (Litex.isSet (Litex.R (M := M))) h_238 h_240))) h_220)
                )
            )
          exact h_220
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_subtraction_x2f_statement_x2e_lit
