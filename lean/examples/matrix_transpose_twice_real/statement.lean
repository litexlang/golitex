import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_transpose_x5f_twice_x5f_real_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_21 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_36 : Litex.In _value_i3 (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_19 h_21)), (by
  let _object_h37 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_19 h_21)))
  have h_37 : Litex.In _value_i3 _object_h37 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_19 h_21) _object_h37 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_19 h_21))) h_36)
        )
    )
  let _object_w112 := (let _wd_1_0 := (Litex.transpose _value_i3 _value_i1 _value_i2 h_19 h_21 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
    exact (show Litex.In _value_i3 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i10 : M.Value) (_raw_i11 : M.Value), M.mem _raw_i10 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i11 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) _raw_i10 _raw_i11) → True := (by
          intro _raw_i10 _raw_i11 h_240 h_245 _
          let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_240)
          have h_240 : Litex.In _value_i10 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_240
          have h_241 : Litex.In _value_i10 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i10 h_240).1
                )
            )
          have h_242 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i10 h_240).2.1
                )
            )
          have h_243 : Litex.Le _value_i10 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i10 h_240).2.2
                )
            )
          have h_244 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_240)
                )
            )
          let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_245)
          have h_245 : Litex.In _value_i11 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_245
          have h_246 : Litex.In _value_i11 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i11 h_245).1
                )
            )
          have h_247 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i11 h_245).2.1
                )
            )
          have h_248 : Litex.Le _value_i11 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i11 h_245).2.2
                )
            )
          have h_249 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_245)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_37))))));
  let _wd_1_1 := _value_i2;
  let _wd_1_2 := _value_i1;
  (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_21 h_19 (by
    let _atomic_wd_1_0 := (Litex.transpose _value_i3 _wd_1_2 _wd_1_1 h_19 h_21 (by
      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
      exact (show Litex.In _value_i3 _atomic_wd_2_1 from (Litex.functionRealToComplex (by
        let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i16 : M.Value) (_raw_i17 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))) → M.mem _raw_i17 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21))) → ((fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True) _raw_i16 _raw_i17) → True := (by
            intro _raw_i16 _raw_i17 h_477 h_482 _
            let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_477)
            have h_477 : Litex.In _value_i16 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) := h_477
            have h_478 : Litex.In _value_i16 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i16 h_477).1
                  )
              )
            have h_479 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i16 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i16 h_477).2.1
                  )
              )
            have h_480 : Litex.Le _value_i16 _wd_1_2 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i16 h_477).2.2
                  )
              )
            have h_481 : Litex.In _value_i16 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i16 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_477)
                  )
              )
            let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_482)
            have h_482 : Litex.In _value_i17 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) := h_482
            have h_483 : Litex.In _value_i17 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i17 h_482).1
                  )
              )
            have h_484 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i17 h_482).2.1
                  )
              )
            have h_485 : Litex.Le _value_i17 _wd_1_1 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i17 h_482).2.2
                  )
              )
            have h_486 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_482)
                  )
              )
            exact True.intro);
          Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))] (by
          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)))
          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
        exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
          let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
          let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
          exact (show Litex.Same _left _right from rfl)) h_37))))))
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_21 h_19)
    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i22 : M.Value) (_raw_i23 : M.Value), M.mem _raw_i22 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))) → M.mem _raw_i23 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21))) → ((fun (_raw_i22 : M.Value) (_raw_i23 : M.Value) => True) _raw_i22 _raw_i23) → True := (by
          intro _raw_i22 _raw_i23 h_586 h_591 _
          let _value_i22 := Litex.semanticObject (M := M) _raw_i22 (M.member_isSet h_586)
          have h_586 : Litex.In _value_i22 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) := h_586
          have h_587 : Litex.In _value_i22 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i22 h_586).1
                )
            )
          have h_588 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i22 h_586).2.1
                )
            )
          have h_589 : Litex.Le _value_i22 _wd_1_2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i22 h_586).2.2
                )
            )
          have h_590 : Litex.In _value_i22 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i22 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_586)
                )
            )
          let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_591)
          have h_591 : Litex.In _value_i23 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) := h_591
          have h_592 : Litex.In _value_i23 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i23 h_591).1
                )
            )
          have h_593 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i23 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i23 h_591).2.1
                )
            )
          have h_594 : Litex.Le _value_i23 _wd_1_1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i23 h_591).2.2
                )
            )
          have h_595 : Litex.In _value_i23 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i23 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_591)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i22 : M.Value) (_raw_i23 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_37)))))))))
  exact (by
    let _atomic_wd_1_0 := _object_w112
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_19 h_21)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_19 _Host_i2 _rep_i2 _value_i2 h_21 _Host_i3 _rep_i3 _value_i3 h_36
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
          let _object_h37 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_19 h_21)))
          have h_37 : Litex.In _value_i3 _object_h37 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_19 h_21) _object_h37 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_19 h_21))) h_36)
                )
            )
          let _object_w112 := (let _wd_1_0 := (Litex.transpose _value_i3 _value_i1 _value_i2 h_19 h_21 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
            exact (show Litex.In _value_i3 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i10 : M.Value) (_raw_i11 : M.Value), M.mem _raw_i10 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i11 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) _raw_i10 _raw_i11) → True := (by
                  intro _raw_i10 _raw_i11 h_240 h_245 _
                  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_240)
                  have h_240 : Litex.In _value_i10 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_240
                  have h_241 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i10 h_240).1
                        )
                    )
                  have h_242 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i10 h_240).2.1
                        )
                    )
                  have h_243 : Litex.Le _value_i10 _value_i1 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i10 h_240).2.2
                        )
                    )
                  have h_244 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_240)
                        )
                    )
                  let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_245)
                  have h_245 : Litex.In _value_i11 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_245
                  have h_246 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i11 h_245).1
                        )
                    )
                  have h_247 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i11 h_245).2.1
                        )
                    )
                  have h_248 : Litex.Le _value_i11 _value_i2 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i11 h_245).2.2
                        )
                    )
                  have h_249 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_245)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_37))))));
          let _wd_1_1 := _value_i2;
          let _wd_1_2 := _value_i1;
          (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_21 h_19 (by
            let _atomic_wd_1_0 := (Litex.transpose _value_i3 _wd_1_2 _wd_1_1 h_19 h_21 (by
              let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
              exact (show Litex.In _value_i3 _atomic_wd_2_1 from (Litex.functionRealToComplex (by
                let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i16 : M.Value) (_raw_i17 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))) → M.mem _raw_i17 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21))) → ((fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True) _raw_i16 _raw_i17) → True := (by
                    intro _raw_i16 _raw_i17 h_477 h_482 _
                    let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_477)
                    have h_477 : Litex.In _value_i16 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) := h_477
                    have h_478 : Litex.In _value_i16 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i16 h_477).1
                          )
                      )
                    have h_479 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i16 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i16 h_477).2.1
                          )
                      )
                    have h_480 : Litex.Le _value_i16 _wd_1_2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i16 h_477).2.2
                          )
                      )
                    have h_481 : Litex.In _value_i16 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i16 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_477)
                          )
                      )
                    let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_482)
                    have h_482 : Litex.In _value_i17 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) := h_482
                    have h_483 : Litex.In _value_i17 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i17 h_482).1
                          )
                      )
                    have h_484 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i17 h_482).2.1
                          )
                      )
                    have h_485 : Litex.Le _value_i17 _wd_1_1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i17 h_482).2.2
                          )
                      )
                    have h_486 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_482)
                          )
                      )
                    exact True.intro);
                  Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))] (by
                  have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)))
                  have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                  let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                  let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                  exact (show Litex.Same _left _right from rfl)) h_37))))))
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_21 h_19)
            exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i22 : M.Value) (_raw_i23 : M.Value), M.mem _raw_i22 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))) → M.mem _raw_i23 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21))) → ((fun (_raw_i22 : M.Value) (_raw_i23 : M.Value) => True) _raw_i22 _raw_i23) → True := (by
                  intro _raw_i22 _raw_i23 h_586 h_591 _
                  let _value_i22 := Litex.semanticObject (M := M) _raw_i22 (M.member_isSet h_586)
                  have h_586 : Litex.In _value_i22 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) := h_586
                  have h_587 : Litex.In _value_i22 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i22 h_586).1
                        )
                    )
                  have h_588 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i22 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i22 h_586).2.1
                        )
                    )
                  have h_589 : Litex.Le _value_i22 _wd_1_2 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i22 h_586).2.2
                        )
                    )
                  have h_590 : Litex.In _value_i22 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i22 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_586)
                        )
                    )
                  let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_591)
                  have h_591 : Litex.In _value_i23 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) := h_591
                  have h_592 : Litex.In _value_i23 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i23 h_591).1
                        )
                    )
                  have h_593 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i23 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i23 h_591).2.1
                        )
                    )
                  have h_594 : Litex.Le _value_i23 _wd_1_1 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i23 h_591).2.2
                        )
                    )
                  have h_595 : Litex.In _value_i23 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i23 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_591)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i22 : M.Value) (_raw_i23 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_37)))))))))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w112
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_19 h_21)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w112
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_19 h_21)
                    exact (by
                      let _membership_function := (let _wd_1_0 := (Litex.transpose _value_i3 _value_i1 _value_i2 h_19 h_21 (by
                        let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
                        exact (show Litex.In _value_i3 _atomic_wd_2_1 from (Litex.functionRealToComplex (by
                          let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i42 : M.Value) (_raw_i43 : M.Value), M.mem _raw_i42 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i43 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i42 : M.Value) (_raw_i43 : M.Value) => True) _raw_i42 _raw_i43) → True := (by
                              intro _raw_i42 _raw_i43 h_919 h_924 _
                              let _value_i42 := Litex.semanticObject (M := M) _raw_i42 (M.member_isSet h_919)
                              have h_919 : Litex.In _value_i42 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_919
                              have h_920 : Litex.In _value_i42 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i42 h_919).1
                                    )
                                )
                              have h_921 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i42 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i42 h_919).2.1
                                    )
                                )
                              have h_922 : Litex.Le _value_i42 _value_i1 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i42 h_919).2.2
                                    )
                                )
                              have h_923 : Litex.In _value_i42 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i42 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_919)
                                    )
                                )
                              let _value_i43 := Litex.semanticObject (M := M) _raw_i43 (M.member_isSet h_924)
                              have h_924 : Litex.In _value_i43 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_924
                              have h_925 : Litex.In _value_i43 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i43 h_924).1
                                    )
                                )
                              have h_926 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i43 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i43 h_924).2.1
                                    )
                                )
                              have h_927 : Litex.Le _value_i43 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i43 h_924).2.2
                                    )
                                )
                              have h_928 : Litex.In _value_i43 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i43 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_924)
                                    )
                                )
                              exact True.intro);
                            Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i42 : M.Value) (_raw_i43 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                          exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                            let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                            let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                            exact (show Litex.Same _left _right from rfl)) h_37))))));
                      let _wd_1_1 := _value_i2;
                      let _wd_1_2 := _value_i1;
                      (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_21 h_19 (by
                        let _atomic_wd_2_0 := (Litex.transpose _value_i3 _wd_1_2 _wd_1_1 h_19 h_21 (by
                          let _atomic_wd_3_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
                          exact (show Litex.In _value_i3 _atomic_wd_3_1 from (Litex.functionRealToComplex (by
                            let _atomic_wd_4_1 := (let _checked_header : ∀ (_raw_i48 : M.Value) (_raw_i49 : M.Value), M.mem _raw_i48 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))) → M.mem _raw_i49 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21))) → ((fun (_raw_i48 : M.Value) (_raw_i49 : M.Value) => True) _raw_i48 _raw_i49) → True := (by
                                intro _raw_i48 _raw_i49 h_1156 h_1161 _
                                let _value_i48 := Litex.semanticObject (M := M) _raw_i48 (M.member_isSet h_1156)
                                have h_1156 : Litex.In _value_i48 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) := h_1156
                                have h_1157 : Litex.In _value_i48 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i48 h_1156).1
                                      )
                                  )
                                have h_1158 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i48 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i48 h_1156).2.1
                                      )
                                  )
                                have h_1159 : Litex.Le _value_i48 _wd_1_2 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i48 h_1156).2.2
                                      )
                                  )
                                have h_1160 : Litex.In _value_i48 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i48 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1156)
                                      )
                                  )
                                let _value_i49 := Litex.semanticObject (M := M) _raw_i49 (M.member_isSet h_1161)
                                have h_1161 : Litex.In _value_i49 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) := h_1161
                                have h_1162 : Litex.In _value_i49 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i49 h_1161).1
                                      )
                                  )
                                have h_1163 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i49 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i49 h_1161).2.1
                                      )
                                  )
                                have h_1164 : Litex.Le _value_i49 _wd_1_1 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i49 h_1161).2.2
                                      )
                                  )
                                have h_1165 : Litex.In _value_i49 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i49 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1161)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))] (by
                              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)))
                              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))
                              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i48 : M.Value) (_raw_i49 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                            exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_4_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_4_1
                              exact (show Litex.Same _left _right from rfl)) h_37))))))
                        let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_21 h_19)
                        exact (show Litex.In _atomic_wd_2_0 _atomic_wd_2_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_2_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
                          let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i54 : M.Value) (_raw_i55 : M.Value), M.mem _raw_i54 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))) → M.mem _raw_i55 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21))) → ((fun (_raw_i54 : M.Value) (_raw_i55 : M.Value) => True) _raw_i54 _raw_i55) → True := (by
                              intro _raw_i54 _raw_i55 h_1265 h_1270 _
                              let _value_i54 := Litex.semanticObject (M := M) _raw_i54 (M.member_isSet h_1265)
                              have h_1265 : Litex.In _value_i54 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) := h_1265
                              have h_1266 : Litex.In _value_i54 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i54 h_1265).1
                                    )
                                )
                              have h_1267 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i54 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i54 h_1265).2.1
                                    )
                                )
                              have h_1268 : Litex.Le _value_i54 _wd_1_2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i54 h_1265).2.2
                                    )
                                )
                              have h_1269 : Litex.In _value_i54 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i54 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1265)
                                    )
                                )
                              let _value_i55 := Litex.semanticObject (M := M) _raw_i55 (M.member_isSet h_1270)
                              have h_1270 : Litex.In _value_i55 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) := h_1270
                              have h_1271 : Litex.In _value_i55 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i55 h_1270).1
                                    )
                                )
                              have h_1272 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i55 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i55 h_1270).2.1
                                    )
                                )
                              have h_1273 : Litex.Le _value_i55 _wd_1_1 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i55 h_1270).2.2
                                    )
                                )
                              have h_1274 : Litex.In _value_i55 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i55 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1270)
                                    )
                                )
                              exact True.intro);
                            Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))] (by
                            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)))
                            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))
                            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i54 : M.Value) (_raw_i55 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                          exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                            let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                            let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                            exact (show Litex.Same _left _right from rfl)) h_37)))))))))
                      let _membership_target := (let _checked_header : ∀ (_raw_i36 : M.Value) (_raw_i37 : M.Value), M.mem _raw_i36 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i37 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i36 : M.Value) (_raw_i37 : M.Value) => True) _raw_i36 _raw_i37) → True := (by
                          intro _raw_i36 _raw_i37 h_1344 h_1349 _
                          let _value_i36 := Litex.semanticObject (M := M) _raw_i36 (M.member_isSet h_1344)
                          have h_1344 : Litex.In _value_i36 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_1344
                          have h_1345 : Litex.In _value_i36 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i36 h_1344).1
                                )
                            )
                          have h_1346 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i36 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i36 h_1344).2.1
                                )
                            )
                          have h_1347 : Litex.Le _value_i36 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i36 h_1344).2.2
                                )
                            )
                          have h_1348 : Litex.In _value_i36 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i36 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1344)
                                )
                            )
                          let _value_i37 := Litex.semanticObject (M := M) _raw_i37 (M.member_isSet h_1349)
                          have h_1349 : Litex.In _value_i37 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_1349
                          have h_1350 : Litex.In _value_i37 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i37 h_1349).1
                                )
                            )
                          have h_1351 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i37 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i37 h_1349).2.1
                                )
                            )
                          have h_1352 : Litex.Le _value_i37 _value_i2 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i37 h_1349).2.2
                                )
                            )
                          have h_1353 : Litex.In _value_i37 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i37 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1349)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i36 : M.Value) (_raw_i37 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      have h_2312 : ∀ {_Host_i36 : Type _} [_rep_i36 : Litex.Representation M _Host_i36] (_value_i36 : Litex.Obj (M := M) _Host_i36) (h_2712 : Litex.In _value_i36 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) {_Host_i37 : Type _} [_rep_i37 : Litex.Representation M _Host_i37] (_value_i37 : Litex.Obj (M := M) _Host_i37) (h_2764 : Litex.In _value_i37 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))), (by
                        let _object_w110 := (let _litex_matrix_head := (let _wd_1_0 := (Litex.transpose _value_i3 _value_i1 _value_i2 h_19 h_21 (by
                          let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
                          exact (show Litex.In _value_i3 _atomic_wd_2_1 from (Litex.functionRealToComplex (by
                            let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i96 : M.Value) (_raw_i97 : M.Value), M.mem _raw_i96 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i97 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i96 : M.Value) (_raw_i97 : M.Value) => True) _raw_i96 _raw_i97) → True := (by
                                intro _raw_i96 _raw_i97 h_2953 h_2958 _
                                let _value_i96 := Litex.semanticObject (M := M) _raw_i96 (M.member_isSet h_2953)
                                have h_2953 : Litex.In _value_i96 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_2953
                                have h_2954 : Litex.In _value_i96 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i96 h_2953).1
                                      )
                                  )
                                have h_2955 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i96 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i96 h_2953).2.1
                                      )
                                  )
                                have h_2956 : Litex.Le _value_i96 _value_i1 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i96 h_2953).2.2
                                      )
                                  )
                                have h_2957 : Litex.In _value_i96 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i96 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2953)
                                      )
                                  )
                                let _value_i97 := Litex.semanticObject (M := M) _raw_i97 (M.member_isSet h_2958)
                                have h_2958 : Litex.In _value_i97 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_2958
                                have h_2959 : Litex.In _value_i97 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i97 h_2958).1
                                      )
                                  )
                                have h_2960 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i97 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i97 h_2958).2.1
                                      )
                                  )
                                have h_2961 : Litex.Le _value_i97 _value_i2 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i97 h_2958).2.2
                                      )
                                  )
                                have h_2962 : Litex.In _value_i97 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i97 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2958)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i96 : M.Value) (_raw_i97 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                            exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                              exact (show Litex.Same _left _right from rfl)) h_37))))));
                        let _wd_1_1 := _value_i2;
                        let _wd_1_2 := _value_i1;
                        (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_21 h_19 (by
                          let _atomic_wd_2_0 := (Litex.transpose _value_i3 _wd_1_2 _wd_1_1 h_19 h_21 (by
                            let _atomic_wd_3_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
                            exact (show Litex.In _value_i3 _atomic_wd_3_1 from (Litex.functionRealToComplex (by
                              let _atomic_wd_4_1 := (let _checked_header : ∀ (_raw_i102 : M.Value) (_raw_i103 : M.Value), M.mem _raw_i102 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i103 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i102 : M.Value) (_raw_i103 : M.Value) => True) _raw_i102 _raw_i103) → True := (by
                                  intro _raw_i102 _raw_i103 h_3208 h_3213 _
                                  let _value_i102 := Litex.semanticObject (M := M) _raw_i102 (M.member_isSet h_3208)
                                  have h_3208 : Litex.In _value_i102 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_3208
                                  have h_3209 : Litex.In _value_i102 (Litex.Z (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i102 h_3208).1
                                        )
                                    )
                                  have h_3210 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i102 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i102 h_3208).2.1
                                        )
                                    )
                                  have h_3211 : Litex.Le _value_i102 _wd_1_2 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i102 h_3208).2.2
                                        )
                                    )
                                  have h_3212 : Litex.In _value_i102 (Litex.NPos (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i102 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3208)
                                        )
                                    )
                                  let _value_i103 := Litex.semanticObject (M := M) _raw_i103 (M.member_isSet h_3213)
                                  have h_3213 : Litex.In _value_i103 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_3213
                                  have h_3214 : Litex.In _value_i103 (Litex.Z (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i103 h_3213).1
                                        )
                                    )
                                  have h_3215 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i103 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i103 h_3213).2.1
                                        )
                                    )
                                  have h_3216 : Litex.Le _value_i103 _wd_1_1 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i103 h_3213).2.2
                                        )
                                    )
                                  have h_3217 : Litex.In _value_i103 (Litex.NPos (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i103 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3213)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i102 : M.Value) (_raw_i103 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                              exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_4_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_4_1
                                exact (show Litex.Same _left _right from rfl)) h_37))))))
                          let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_21 h_19)
                          exact (show Litex.In _atomic_wd_2_0 _atomic_wd_2_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_2_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
                            let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i108 : M.Value) (_raw_i109 : M.Value), M.mem _raw_i108 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i109 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i108 : M.Value) (_raw_i109 : M.Value) => True) _raw_i108 _raw_i109) → True := (by
                                intro _raw_i108 _raw_i109 h_3320 h_3325 _
                                let _value_i108 := Litex.semanticObject (M := M) _raw_i108 (M.member_isSet h_3320)
                                have h_3320 : Litex.In _value_i108 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_3320
                                have h_3321 : Litex.In _value_i108 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i108 h_3320).1
                                      )
                                  )
                                have h_3322 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i108 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i108 h_3320).2.1
                                      )
                                  )
                                have h_3323 : Litex.Le _value_i108 _wd_1_2 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i108 h_3320).2.2
                                      )
                                  )
                                have h_3324 : Litex.In _value_i108 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i108 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3320)
                                      )
                                  )
                                let _value_i109 := Litex.semanticObject (M := M) _raw_i109 (M.member_isSet h_3325)
                                have h_3325 : Litex.In _value_i109 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_3325
                                have h_3326 : Litex.In _value_i109 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i109 h_3325).1
                                      )
                                  )
                                have h_3327 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i109 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i109 h_3325).2.1
                                      )
                                  )
                                have h_3328 : Litex.Le _value_i109 _wd_1_1 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i109 h_3325).2.2
                                      )
                                  )
                                have h_3329 : Litex.In _value_i109 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i109 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3325)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i108 : M.Value) (_raw_i109 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                            exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                              exact (show Litex.Same _left _right from rfl)) h_37)))))))));
                        (let _litex_call_arg_0 := _value_i36;
                        let _litex_call_arg_1 := _value_i37;
                        Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.transposeInRealFnSet _litex_matrix_head (by
                          let _atomic_wd_2_0 := (Litex.transpose _value_i3 _value_i1 _value_i2 h_19 h_21 (by
                            let _atomic_wd_3_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
                            exact (show Litex.In _value_i3 _atomic_wd_3_1 from (Litex.functionRealToComplex (by
                              let _atomic_wd_4_1 := (let _checked_header : ∀ (_raw_i118 : M.Value) (_raw_i119 : M.Value), M.mem _raw_i118 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i119 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i118 : M.Value) (_raw_i119 : M.Value) => True) _raw_i118 _raw_i119) → True := (by
                                  intro _raw_i118 _raw_i119 h_3539 h_3544 _
                                  let _value_i118 := Litex.semanticObject (M := M) _raw_i118 (M.member_isSet h_3539)
                                  have h_3539 : Litex.In _value_i118 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_3539
                                  have h_3540 : Litex.In _value_i118 (Litex.Z (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i118 h_3539).1
                                        )
                                    )
                                  have h_3541 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i118 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i118 h_3539).2.1
                                        )
                                    )
                                  have h_3542 : Litex.Le _value_i118 _value_i1 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i118 h_3539).2.2
                                        )
                                    )
                                  have h_3543 : Litex.In _value_i118 (Litex.NPos (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i118 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3539)
                                        )
                                    )
                                  let _value_i119 := Litex.semanticObject (M := M) _raw_i119 (M.member_isSet h_3544)
                                  have h_3544 : Litex.In _value_i119 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_3544
                                  have h_3545 : Litex.In _value_i119 (Litex.Z (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i119 h_3544).1
                                        )
                                    )
                                  have h_3546 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i119 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i119 h_3544).2.1
                                        )
                                    )
                                  have h_3547 : Litex.Le _value_i119 _value_i2 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i119 h_3544).2.2
                                        )
                                    )
                                  have h_3548 : Litex.In _value_i119 (Litex.NPos (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i119 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3544)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i118 : M.Value) (_raw_i119 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                              exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_4_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_4_1
                                exact (show Litex.Same _left _right from rfl)) h_37))))))
                          let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i112 : M.Value) (_raw_i113 : M.Value), M.mem _raw_i112 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → M.mem _raw_i113 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → ((fun (_raw_i112 : M.Value) (_raw_i113 : M.Value) => True) _raw_i112 _raw_i113) → True := (by
                              intro _raw_i112 _raw_i113 h_3573 h_3578 _
                              let _value_i112 := Litex.semanticObject (M := M) _raw_i112 (M.member_isSet h_3573)
                              have h_3573 : Litex.In _value_i112 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_3573
                              have h_3574 : Litex.In _value_i112 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i112 h_3573).1
                                    )
                                )
                              have h_3575 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i112 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i112 h_3573).2.1
                                    )
                                )
                              have h_3576 : Litex.Le _value_i112 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i112 h_3573).2.2
                                    )
                                )
                              have h_3577 : Litex.In _value_i112 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i112 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3573)
                                    )
                                )
                              let _value_i113 := Litex.semanticObject (M := M) _raw_i113 (M.member_isSet h_3578)
                              have h_3578 : Litex.In _value_i113 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_3578
                              have h_3579 : Litex.In _value_i113 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i113 h_3578).1
                                    )
                                )
                              have h_3580 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i113 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i113 h_3578).2.1
                                    )
                                )
                              have h_3581 : Litex.Le _value_i113 _value_i1 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i113 h_3578).2.2
                                    )
                                )
                              have h_3582 : Litex.In _value_i113 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i113 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3578)
                                    )
                                )
                              exact True.intro);
                            Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))] (by
                            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i112 : M.Value) (_raw_i113 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                          exact (show Litex.In _atomic_wd_2_0 _atomic_wd_2_1 from (let _litex_matrix := _atomic_wd_2_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
                            let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i120 : M.Value) (_raw_i121 : M.Value), M.mem _raw_i120 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i121 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i120 : M.Value) (_raw_i121 : M.Value) => True) _raw_i120 _raw_i121) → True := (by
                                intro _raw_i120 _raw_i121 h_3624 h_3629 _
                                let _value_i120 := Litex.semanticObject (M := M) _raw_i120 (M.member_isSet h_3624)
                                have h_3624 : Litex.In _value_i120 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_3624
                                have h_3625 : Litex.In _value_i120 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i120 h_3624).1
                                      )
                                  )
                                have h_3626 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i120 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i120 h_3624).2.1
                                      )
                                  )
                                have h_3627 : Litex.Le _value_i120 _value_i1 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i120 h_3624).2.2
                                      )
                                  )
                                have h_3628 : Litex.In _value_i120 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i120 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3624)
                                      )
                                  )
                                let _value_i121 := Litex.semanticObject (M := M) _raw_i121 (M.member_isSet h_3629)
                                have h_3629 : Litex.In _value_i121 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_3629
                                have h_3630 : Litex.In _value_i121 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i121 h_3629).1
                                      )
                                  )
                                have h_3631 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i121 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i121 h_3629).2.1
                                      )
                                  )
                                have h_3632 : Litex.Le _value_i121 _value_i2 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i121 h_3629).2.2
                                      )
                                  )
                                have h_3633 : Litex.In _value_i121 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i121 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3629)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i120 : M.Value) (_raw_i121 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                            exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                              exact (show Litex.Same _left _right from rfl)) h_37))))))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                          exact h_2712) (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))
                          exact h_2764)), True.intro⟩)))
                        exact (by
                          let _atomic_wd_2_0 := _object_w110
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                      ) := (by
                        intro _Host_i36 _rep_i36 _value_i36 h_2712 _Host_i37 _rep_i37 _value_i37 h_2764
                        have h_2713 : Litex.In _value_i36 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i36 h_2712).1
                              )
                          )
                        have h_2714 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i36 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i36 h_2712).2.1
                              )
                          )
                        have h_2715 : Litex.Le _value_i36 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i36 h_2712).2.2
                              )
                          )
                        have h_2716 : Litex.In _value_i36 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i36 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2712)
                              )
                          )
                        have h_2765 : Litex.In _value_i37 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i37 h_2764).1
                              )
                          )
                        have h_2766 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i37 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i37 h_2764).2.1
                              )
                          )
                        have h_2767 : Litex.Le _value_i37 _value_i2 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i37 h_2764).2.2
                              )
                          )
                        have h_2768 : Litex.In _value_i37 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i37 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2764)
                              )
                          )
                        let _object_w110 := (let _litex_matrix_head := (let _wd_1_0 := (Litex.transpose _value_i3 _value_i1 _value_i2 h_19 h_21 (by
                          let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
                          exact (show Litex.In _value_i3 _atomic_wd_2_1 from (Litex.functionRealToComplex (by
                            let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i96 : M.Value) (_raw_i97 : M.Value), M.mem _raw_i96 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i97 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i96 : M.Value) (_raw_i97 : M.Value) => True) _raw_i96 _raw_i97) → True := (by
                                intro _raw_i96 _raw_i97 h_2953 h_2958 _
                                let _value_i96 := Litex.semanticObject (M := M) _raw_i96 (M.member_isSet h_2953)
                                have h_2953 : Litex.In _value_i96 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_2953
                                have h_2954 : Litex.In _value_i96 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i96 h_2953).1
                                      )
                                  )
                                have h_2955 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i96 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i96 h_2953).2.1
                                      )
                                  )
                                have h_2956 : Litex.Le _value_i96 _value_i1 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i96 h_2953).2.2
                                      )
                                  )
                                have h_2957 : Litex.In _value_i96 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i96 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2953)
                                      )
                                  )
                                let _value_i97 := Litex.semanticObject (M := M) _raw_i97 (M.member_isSet h_2958)
                                have h_2958 : Litex.In _value_i97 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_2958
                                have h_2959 : Litex.In _value_i97 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i97 h_2958).1
                                      )
                                  )
                                have h_2960 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i97 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i97 h_2958).2.1
                                      )
                                  )
                                have h_2961 : Litex.Le _value_i97 _value_i2 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i97 h_2958).2.2
                                      )
                                  )
                                have h_2962 : Litex.In _value_i97 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i97 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2958)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i96 : M.Value) (_raw_i97 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                            exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                              exact (show Litex.Same _left _right from rfl)) h_37))))));
                        let _wd_1_1 := _value_i2;
                        let _wd_1_2 := _value_i1;
                        (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_21 h_19 (by
                          let _atomic_wd_2_0 := (Litex.transpose _value_i3 _wd_1_2 _wd_1_1 h_19 h_21 (by
                            let _atomic_wd_3_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
                            exact (show Litex.In _value_i3 _atomic_wd_3_1 from (Litex.functionRealToComplex (by
                              let _atomic_wd_4_1 := (let _checked_header : ∀ (_raw_i102 : M.Value) (_raw_i103 : M.Value), M.mem _raw_i102 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i103 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i102 : M.Value) (_raw_i103 : M.Value) => True) _raw_i102 _raw_i103) → True := (by
                                  intro _raw_i102 _raw_i103 h_3208 h_3213 _
                                  let _value_i102 := Litex.semanticObject (M := M) _raw_i102 (M.member_isSet h_3208)
                                  have h_3208 : Litex.In _value_i102 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_3208
                                  have h_3209 : Litex.In _value_i102 (Litex.Z (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i102 h_3208).1
                                        )
                                    )
                                  have h_3210 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i102 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i102 h_3208).2.1
                                        )
                                    )
                                  have h_3211 : Litex.Le _value_i102 _wd_1_2 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i102 h_3208).2.2
                                        )
                                    )
                                  have h_3212 : Litex.In _value_i102 (Litex.NPos (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i102 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3208)
                                        )
                                    )
                                  let _value_i103 := Litex.semanticObject (M := M) _raw_i103 (M.member_isSet h_3213)
                                  have h_3213 : Litex.In _value_i103 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_3213
                                  have h_3214 : Litex.In _value_i103 (Litex.Z (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i103 h_3213).1
                                        )
                                    )
                                  have h_3215 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i103 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i103 h_3213).2.1
                                        )
                                    )
                                  have h_3216 : Litex.Le _value_i103 _wd_1_1 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i103 h_3213).2.2
                                        )
                                    )
                                  have h_3217 : Litex.In _value_i103 (Litex.NPos (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i103 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3213)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i102 : M.Value) (_raw_i103 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                              exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_4_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_4_1
                                exact (show Litex.Same _left _right from rfl)) h_37))))))
                          let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_21 h_19)
                          exact (show Litex.In _atomic_wd_2_0 _atomic_wd_2_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_2_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
                            let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i108 : M.Value) (_raw_i109 : M.Value), M.mem _raw_i108 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i109 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i108 : M.Value) (_raw_i109 : M.Value) => True) _raw_i108 _raw_i109) → True := (by
                                intro _raw_i108 _raw_i109 h_3320 h_3325 _
                                let _value_i108 := Litex.semanticObject (M := M) _raw_i108 (M.member_isSet h_3320)
                                have h_3320 : Litex.In _value_i108 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_3320
                                have h_3321 : Litex.In _value_i108 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i108 h_3320).1
                                      )
                                  )
                                have h_3322 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i108 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i108 h_3320).2.1
                                      )
                                  )
                                have h_3323 : Litex.Le _value_i108 _wd_1_2 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i108 h_3320).2.2
                                      )
                                  )
                                have h_3324 : Litex.In _value_i108 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i108 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3320)
                                      )
                                  )
                                let _value_i109 := Litex.semanticObject (M := M) _raw_i109 (M.member_isSet h_3325)
                                have h_3325 : Litex.In _value_i109 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_3325
                                have h_3326 : Litex.In _value_i109 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i109 h_3325).1
                                      )
                                  )
                                have h_3327 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i109 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i109 h_3325).2.1
                                      )
                                  )
                                have h_3328 : Litex.Le _value_i109 _wd_1_1 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i109 h_3325).2.2
                                      )
                                  )
                                have h_3329 : Litex.In _value_i109 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i109 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3325)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i108 : M.Value) (_raw_i109 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                            exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                              exact (show Litex.Same _left _right from rfl)) h_37)))))))));
                        (let _litex_call_arg_0 := _value_i36;
                        let _litex_call_arg_1 := _value_i37;
                        Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.transposeInRealFnSet _litex_matrix_head (by
                          let _atomic_wd_2_0 := (Litex.transpose _value_i3 _value_i1 _value_i2 h_19 h_21 (by
                            let _atomic_wd_3_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
                            exact (show Litex.In _value_i3 _atomic_wd_3_1 from (Litex.functionRealToComplex (by
                              let _atomic_wd_4_1 := (let _checked_header : ∀ (_raw_i118 : M.Value) (_raw_i119 : M.Value), M.mem _raw_i118 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i119 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i118 : M.Value) (_raw_i119 : M.Value) => True) _raw_i118 _raw_i119) → True := (by
                                  intro _raw_i118 _raw_i119 h_3539 h_3544 _
                                  let _value_i118 := Litex.semanticObject (M := M) _raw_i118 (M.member_isSet h_3539)
                                  have h_3539 : Litex.In _value_i118 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_3539
                                  have h_3540 : Litex.In _value_i118 (Litex.Z (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i118 h_3539).1
                                        )
                                    )
                                  have h_3541 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i118 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i118 h_3539).2.1
                                        )
                                    )
                                  have h_3542 : Litex.Le _value_i118 _value_i1 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i118 h_3539).2.2
                                        )
                                    )
                                  have h_3543 : Litex.In _value_i118 (Litex.NPos (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i118 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3539)
                                        )
                                    )
                                  let _value_i119 := Litex.semanticObject (M := M) _raw_i119 (M.member_isSet h_3544)
                                  have h_3544 : Litex.In _value_i119 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_3544
                                  have h_3545 : Litex.In _value_i119 (Litex.Z (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i119 h_3544).1
                                        )
                                    )
                                  have h_3546 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i119 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i119 h_3544).2.1
                                        )
                                    )
                                  have h_3547 : Litex.Le _value_i119 _value_i2 :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i119 h_3544).2.2
                                        )
                                    )
                                  have h_3548 : Litex.In _value_i119 (Litex.NPos (M := M)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i119 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3544)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i118 : M.Value) (_raw_i119 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                              exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_4_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_4_1
                                exact (show Litex.Same _left _right from rfl)) h_37))))))
                          let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i112 : M.Value) (_raw_i113 : M.Value), M.mem _raw_i112 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → M.mem _raw_i113 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → ((fun (_raw_i112 : M.Value) (_raw_i113 : M.Value) => True) _raw_i112 _raw_i113) → True := (by
                              intro _raw_i112 _raw_i113 h_3573 h_3578 _
                              let _value_i112 := Litex.semanticObject (M := M) _raw_i112 (M.member_isSet h_3573)
                              have h_3573 : Litex.In _value_i112 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_3573
                              have h_3574 : Litex.In _value_i112 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i112 h_3573).1
                                    )
                                )
                              have h_3575 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i112 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i112 h_3573).2.1
                                    )
                                )
                              have h_3576 : Litex.Le _value_i112 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i112 h_3573).2.2
                                    )
                                )
                              have h_3577 : Litex.In _value_i112 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i112 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3573)
                                    )
                                )
                              let _value_i113 := Litex.semanticObject (M := M) _raw_i113 (M.member_isSet h_3578)
                              have h_3578 : Litex.In _value_i113 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_3578
                              have h_3579 : Litex.In _value_i113 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i113 h_3578).1
                                    )
                                )
                              have h_3580 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i113 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i113 h_3578).2.1
                                    )
                                )
                              have h_3581 : Litex.Le _value_i113 _value_i1 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i113 h_3578).2.2
                                    )
                                )
                              have h_3582 : Litex.In _value_i113 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i113 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3578)
                                    )
                                )
                              exact True.intro);
                            Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))] (by
                            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i112 : M.Value) (_raw_i113 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                          exact (show Litex.In _atomic_wd_2_0 _atomic_wd_2_1 from (let _litex_matrix := _atomic_wd_2_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
                            let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i120 : M.Value) (_raw_i121 : M.Value), M.mem _raw_i120 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i121 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i120 : M.Value) (_raw_i121 : M.Value) => True) _raw_i120 _raw_i121) → True := (by
                                intro _raw_i120 _raw_i121 h_3624 h_3629 _
                                let _value_i120 := Litex.semanticObject (M := M) _raw_i120 (M.member_isSet h_3624)
                                have h_3624 : Litex.In _value_i120 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_3624
                                have h_3625 : Litex.In _value_i120 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i120 h_3624).1
                                      )
                                  )
                                have h_3626 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i120 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i120 h_3624).2.1
                                      )
                                  )
                                have h_3627 : Litex.Le _value_i120 _value_i1 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i120 h_3624).2.2
                                      )
                                  )
                                have h_3628 : Litex.In _value_i120 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i120 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3624)
                                      )
                                  )
                                let _value_i121 := Litex.semanticObject (M := M) _raw_i121 (M.member_isSet h_3629)
                                have h_3629 : Litex.In _value_i121 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_3629
                                have h_3630 : Litex.In _value_i121 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i121 h_3629).1
                                      )
                                  )
                                have h_3631 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i121 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i121 h_3629).2.1
                                      )
                                  )
                                have h_3632 : Litex.Le _value_i121 _value_i2 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i121 h_3629).2.2
                                      )
                                  )
                                have h_3633 : Litex.In _value_i121 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i121 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3629)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i120 : M.Value) (_raw_i121 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                            exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                              exact (show Litex.Same _left _right from rfl)) h_37))))))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                          exact h_2712) (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))
                          exact h_2764)), True.intro⟩)))
                        have h_2313 : (by
                          let _atomic_wd_2_0 := _object_w110
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_2_0 := _object_w110
                                  exact (let _litex_real_matrix := (_atomic_wd_2_0).val.function; let _litex_real_signature := (Litex.matrixEntrywiseSignature _value_i1 _value_i2 .real); (show Litex.In _atomic_wd_2_0 Litex.R from Litex.FunctionSemantics.call_mem _litex_real_signature.domain _litex_real_signature.output (Litex.denote _litex_real_matrix) (Litex.denote (Litex.callArguments2 _value_i36 _value_i37)) (Litex.transposeInRealFnSet _litex_real_matrix (Litex.transposeInRealFnSet ((_atomic_wd_2_0).val.function).val.matrix h_36)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                                  ))) (fun (_litex_input : M.Value) => (fun (_raw_i126 : M.Value) (_raw_i127 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i36 _value_i37))).mpr ⟨(Litex.callArguments2_mem_cart _value_i36 _value_i37 (by
                                    let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                                    exact h_2712) (by
                                    let _atomic_wd_3_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))
                                    exact h_2764)), True.intro⟩))))
                              )
                          )
                        exact h_2313
                      )
                      exact (by
                        let _source_signature := (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i90 : M.Value) (_raw_i91 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))))
                        have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (let _litex_matrix := (let _wd_1_0 := (Litex.transpose _value_i3 _value_i1 _value_i2 h_19 h_21 (by
                        let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
                        exact (show Litex.In _value_i3 _atomic_wd_2_1 from (Litex.functionRealToComplex (by
                          let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i62 : M.Value) (_raw_i63 : M.Value), M.mem _raw_i62 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i63 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i62 : M.Value) (_raw_i63 : M.Value) => True) _raw_i62 _raw_i63) → True := (by
                              intro _raw_i62 _raw_i63 h_1556 h_1561 _
                              let _value_i62 := Litex.semanticObject (M := M) _raw_i62 (M.member_isSet h_1556)
                              have h_1556 : Litex.In _value_i62 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_1556
                              have h_1557 : Litex.In _value_i62 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i62 h_1556).1
                                    )
                                )
                              have h_1558 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i62 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i62 h_1556).2.1
                                    )
                                )
                              have h_1559 : Litex.Le _value_i62 _value_i1 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i62 h_1556).2.2
                                    )
                                )
                              have h_1560 : Litex.In _value_i62 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i62 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1556)
                                    )
                                )
                              let _value_i63 := Litex.semanticObject (M := M) _raw_i63 (M.member_isSet h_1561)
                              have h_1561 : Litex.In _value_i63 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_1561
                              have h_1562 : Litex.In _value_i63 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i63 h_1561).1
                                    )
                                )
                              have h_1563 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i63 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i63 h_1561).2.1
                                    )
                                )
                              have h_1564 : Litex.Le _value_i63 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i63 h_1561).2.2
                                    )
                                )
                              have h_1565 : Litex.In _value_i63 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i63 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1561)
                                    )
                                )
                              exact True.intro);
                            Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i62 : M.Value) (_raw_i63 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                          exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                            let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                            let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                            exact (show Litex.Same _left _right from rfl)) h_37))))));
                      let _wd_1_1 := _value_i2;
                      let _wd_1_2 := _value_i1;
                      (Litex.transpose _wd_1_0 _wd_1_1 _wd_1_2 h_21 h_19 (by
                        let _atomic_wd_2_0 := (Litex.transpose _value_i3 _wd_1_2 _wd_1_1 h_19 h_21 (by
                          let _atomic_wd_3_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_2 _wd_1_1 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
                          exact (show Litex.In _value_i3 _atomic_wd_3_1 from (Litex.functionRealToComplex (by
                            let _atomic_wd_4_1 := (let _checked_header : ∀ (_raw_i68 : M.Value) (_raw_i69 : M.Value), M.mem _raw_i68 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))) → M.mem _raw_i69 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21))) → ((fun (_raw_i68 : M.Value) (_raw_i69 : M.Value) => True) _raw_i68 _raw_i69) → True := (by
                                intro _raw_i68 _raw_i69 h_1793 h_1798 _
                                let _value_i68 := Litex.semanticObject (M := M) _raw_i68 (M.member_isSet h_1793)
                                have h_1793 : Litex.In _value_i68 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) := h_1793
                                have h_1794 : Litex.In _value_i68 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i68 h_1793).1
                                      )
                                  )
                                have h_1795 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i68 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i68 h_1793).2.1
                                      )
                                  )
                                have h_1796 : Litex.Le _value_i68 _wd_1_2 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i68 h_1793).2.2
                                      )
                                  )
                                have h_1797 : Litex.In _value_i68 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i68 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1793)
                                      )
                                  )
                                let _value_i69 := Litex.semanticObject (M := M) _raw_i69 (M.member_isSet h_1798)
                                have h_1798 : Litex.In _value_i69 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) := h_1798
                                have h_1799 : Litex.In _value_i69 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i69 h_1798).1
                                      )
                                  )
                                have h_1800 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i69 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i69 h_1798).2.1
                                      )
                                  )
                                have h_1801 : Litex.Le _value_i69 _wd_1_1 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i69 h_1798).2.2
                                      )
                                  )
                                have h_1802 : Litex.In _value_i69 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i69 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1798)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))] (by
                              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)))
                              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))
                              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i68 : M.Value) (_raw_i69 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                            exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_4_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_4_1
                              exact (show Litex.Same _left _right from rfl)) h_37))))))
                        let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _wd_1_1 _wd_1_2 (Litex.isSet (Litex.C (M := M))) h_21 h_19)
                        exact (show Litex.In _atomic_wd_2_0 _atomic_wd_2_1 from (Litex.functionRealToComplex (let _litex_matrix := _atomic_wd_2_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
                          let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i74 : M.Value) (_raw_i75 : M.Value), M.mem _raw_i74 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))) → M.mem _raw_i75 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21))) → ((fun (_raw_i74 : M.Value) (_raw_i75 : M.Value) => True) _raw_i74 _raw_i75) → True := (by
                              intro _raw_i74 _raw_i75 h_1902 h_1907 _
                              let _value_i74 := Litex.semanticObject (M := M) _raw_i74 (M.member_isSet h_1902)
                              have h_1902 : Litex.In _value_i74 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) := h_1902
                              have h_1903 : Litex.In _value_i74 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i74 h_1902).1
                                    )
                                )
                              have h_1904 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i74 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i74 h_1902).2.1
                                    )
                                )
                              have h_1905 : Litex.Le _value_i74 _wd_1_2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i74 h_1902).2.2
                                    )
                                )
                              have h_1906 : Litex.In _value_i74 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)) _value_i74 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1902)
                                    )
                                )
                              let _value_i75 := Litex.semanticObject (M := M) _raw_i75 (M.member_isSet h_1907)
                              have h_1907 : Litex.In _value_i75 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) := h_1907
                              have h_1908 : Litex.In _value_i75 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i75 h_1907).1
                                    )
                                )
                              have h_1909 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i75 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i75 h_1907).2.1
                                    )
                                )
                              have h_1910 : Litex.Le _value_i75 _wd_1_1 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i75 h_1907).2.2
                                    )
                                )
                              have h_1911 : Litex.In _value_i75 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)) _value_i75 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1907)
                                    )
                                )
                              exact True.intro);
                            Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))] (by
                            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_2 h_19)))
                            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_1 h_21)))
                            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i74 : M.Value) (_raw_i75 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                          exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                            let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                            let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                            exact (show Litex.Same _left _right from rfl)) h_37))))))))); let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
                        let _atomic_wd_2_0 := (Litex.transpose _value_i3 _value_i1 _value_i2 h_19 h_21 (by
                          let _atomic_wd_3_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
                          exact (show Litex.In _value_i3 _atomic_wd_3_1 from (Litex.functionRealToComplex (by
                            let _atomic_wd_4_1 := (let _checked_header : ∀ (_raw_i84 : M.Value) (_raw_i85 : M.Value), M.mem _raw_i84 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i85 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i84 : M.Value) (_raw_i85 : M.Value) => True) _raw_i84 _raw_i85) → True := (by
                                intro _raw_i84 _raw_i85 h_2127 h_2132 _
                                let _value_i84 := Litex.semanticObject (M := M) _raw_i84 (M.member_isSet h_2127)
                                have h_2127 : Litex.In _value_i84 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_2127
                                have h_2128 : Litex.In _value_i84 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i84 h_2127).1
                                      )
                                  )
                                have h_2129 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i84 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i84 h_2127).2.1
                                      )
                                  )
                                have h_2130 : Litex.Le _value_i84 _value_i1 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i84 h_2127).2.2
                                      )
                                  )
                                have h_2131 : Litex.In _value_i84 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i84 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2127)
                                      )
                                  )
                                let _value_i85 := Litex.semanticObject (M := M) _raw_i85 (M.member_isSet h_2132)
                                have h_2132 : Litex.In _value_i85 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_2132
                                have h_2133 : Litex.In _value_i85 (Litex.Z (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i85 h_2132).1
                                      )
                                  )
                                have h_2134 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i85 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i85 h_2132).2.1
                                      )
                                  )
                                have h_2135 : Litex.Le _value_i85 _value_i2 :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i85 h_2132).2.2
                                      )
                                  )
                                have h_2136 : Litex.In _value_i85 (Litex.NPos (M := M)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i85 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2132)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i84 : M.Value) (_raw_i85 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                            exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_4_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_4_1
                              exact (show Litex.Same _left _right from rfl)) h_37))))))
                        let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i78 : M.Value) (_raw_i79 : M.Value), M.mem _raw_i78 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → M.mem _raw_i79 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → ((fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => True) _raw_i78 _raw_i79) → True := (by
                            intro _raw_i78 _raw_i79 h_2206 h_2211 _
                            let _value_i78 := Litex.semanticObject (M := M) _raw_i78 (M.member_isSet h_2206)
                            have h_2206 : Litex.In _value_i78 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_2206
                            have h_2207 : Litex.In _value_i78 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i78 h_2206).1
                                  )
                              )
                            have h_2208 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i78 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i78 h_2206).2.1
                                  )
                              )
                            have h_2209 : Litex.Le _value_i78 _value_i2 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i78 h_2206).2.2
                                  )
                              )
                            have h_2210 : Litex.In _value_i78 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i78 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2206)
                                  )
                              )
                            let _value_i79 := Litex.semanticObject (M := M) _raw_i79 (M.member_isSet h_2211)
                            have h_2211 : Litex.In _value_i79 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_2211
                            have h_2212 : Litex.In _value_i79 (Litex.Z (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i79 h_2211).1
                                  )
                              )
                            have h_2213 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i79 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i79 h_2211).2.1
                                  )
                              )
                            have h_2214 : Litex.Le _value_i79 _value_i1 :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i79 h_2211).2.2
                                  )
                              )
                            have h_2215 : Litex.In _value_i79 (Litex.NPos (M := M)) :=
                              (by
                                litex_checked_step =>
                                  exact (
                                    (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i79 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2211)
                                  )
                              )
                            exact True.intro);
                          Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))] (by
                          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                        )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                        exact (show Litex.In _atomic_wd_2_0 _atomic_wd_2_1 from (let _litex_matrix := _atomic_wd_2_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.transposeInRealFnSet _litex_matrix (by
                          let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i86 : M.Value) (_raw_i87 : M.Value), M.mem _raw_i86 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i87 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i86 : M.Value) (_raw_i87 : M.Value) => True) _raw_i86 _raw_i87) → True := (by
                              intro _raw_i86 _raw_i87 h_2290 h_2295 _
                              let _value_i86 := Litex.semanticObject (M := M) _raw_i86 (M.member_isSet h_2290)
                              have h_2290 : Litex.In _value_i86 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_2290
                              have h_2291 : Litex.In _value_i86 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i86 h_2290).1
                                    )
                                )
                              have h_2292 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i86 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i86 h_2290).2.1
                                    )
                                )
                              have h_2293 : Litex.Le _value_i86 _value_i1 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i86 h_2290).2.2
                                    )
                                )
                              have h_2294 : Litex.In _value_i86 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i86 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2290)
                                    )
                                )
                              let _value_i87 := Litex.semanticObject (M := M) _raw_i87 (M.member_isSet h_2295)
                              have h_2295 : Litex.In _value_i87 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_2295
                              have h_2296 : Litex.In _value_i87 (Litex.Z (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i87 h_2295).1
                                    )
                                )
                              have h_2297 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i87 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i87 h_2295).2.1
                                    )
                                )
                              have h_2298 : Litex.Le _value_i87 _value_i2 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i87 h_2295).2.2
                                    )
                                )
                              have h_2299 : Litex.In _value_i87 (Litex.NPos (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i87 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2295)
                                    )
                                )
                              exact True.intro);
                            Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                          )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i86 : M.Value) (_raw_i87 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                          exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                            let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                            let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
                            exact (show Litex.Same _left _right from rfl)) h_37))))))))
                        have _same_domain : _source_signature.domain = _membership_target.val.domain := (by rfl)
                        change M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _membership_target.val.domain _membership_target.val.output)
                        have _source_graph : M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _source_signature.domain _source_signature.output) := _source_member
                        rw [_same_domain] at _source_graph
                        apply Litex.FunctionSemantics.fnSet_of_returns _source_graph
                        intro _input _hin
                        change M.mem _input (Litex.SetSemantics.sepValue _ _) at _hin
                        obtain ⟨_members, _guard⟩ := (Litex.SetSemantics.sep_members _ _ _).mp _hin
                        obtain ⟨_raw_0, _member_0, _raw_1, _member_1, rfl⟩ := (Litex.FiniteFunction.cart2_members _ _ _).mp _members
                        let _arg_0 := Litex.semanticObject (M := M) _raw_0 (M.member_isSet _member_0)
                        let _arg_1 := Litex.semanticObject (M := M) _raw_1 (M.member_isSet _member_1)
                        exact h_2312 _arg_0 _member_0 _arg_1 _member_1)))
                )
            )
          let _object_h3889 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_19 h_21)))
          have h_3889 : Litex.In _object_w112 _object_h3889 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w112 _object_w112 (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_19 h_21) _object_h3889 (Litex.sameRefl _object_w112) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_19 h_21))) h_1)
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_transpose_x5f_twice_x5f_real_x2f_statement_x2e_lit
