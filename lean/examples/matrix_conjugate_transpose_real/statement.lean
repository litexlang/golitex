import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_conjugate_x5f_transpose_x5f_real_x2f_statement_x2e_lit

universe u v1 v2 v3 v22 v23 v24 v25 v26
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
  let _object_w20 := (Litex.conjugateTranspose _value_i3 _value_i1 _value_i2 h_19 h_21 (by
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
        exact (show Litex.Same _left _right from rfl)) h_37))))))
  let _object_w21 := (Litex.matrixSet (Litex.R (M := M)) _value_i2 _value_i1 (Litex.isSet (Litex.R (M := M))) h_21 h_19)
  exact (by
    let _atomic_wd_1_0 := _object_w20
    let _atomic_wd_1_1 := _object_w21
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
          let _object_w20 := (Litex.conjugateTranspose _value_i3 _value_i1 _value_i2 h_19 h_21 (by
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
                exact (show Litex.Same _left _right from rfl)) h_37))))))
          let _object_w21 := (Litex.matrixSet (Litex.R (M := M)) _value_i2 _value_i1 (Litex.isSet (Litex.R (M := M))) h_21 h_19)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w20
            let _atomic_wd_1_1 := _object_w21
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w20
                    let _atomic_wd_1_1 := _object_w21
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i16 : M.Value) (_raw_i17 : M.Value), M.mem _raw_i16 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))) → M.mem _raw_i17 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21))) → ((fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True) _raw_i16 _raw_i17) → True := (by
                          intro _raw_i16 _raw_i17 h_349 h_354 _
                          let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_349)
                          have h_349 : Litex.In _value_i16 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) := h_349
                          have h_350 : Litex.In _value_i16 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i16 h_349).1
                                )
                            )
                          have h_351 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i16 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i16 h_349).2.1
                                )
                            )
                          have h_352 : Litex.Le _value_i16 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i16 h_349).2.2
                                )
                            )
                          have h_353 : Litex.In _value_i16 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)) _value_i16 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_349)
                                )
                            )
                          let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_354)
                          have h_354 : Litex.In _value_i17 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) := h_354
                          have h_355 : Litex.In _value_i17 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i17 h_354).1
                                )
                            )
                          have h_356 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i17 h_354).2.1
                                )
                            )
                          have h_357 : Litex.Le _value_i17 _value_i2 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i17 h_354).2.2
                                )
                            )
                          have h_358 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)) _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_354)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_21)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i3 _value_i3 _object_h37 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h37
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_37))))))
                )
            )
          let _object_h371 := (Litex.fnSet (Litex.matrixSignature _object_w21))
          have h_371 : Litex.In _object_w20 _object_h371 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w20 _object_w20 _object_w21 _object_h371 (Litex.sameRefl _object_w20) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet _object_w21)) h_1)
                )
            )
          exact h_1
        )
      )
  )

theorem h_373 : ∀ {_Host_i22 : Type v22} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (h_396 : Litex.In _value_i22 (Litex.N (M := M))) {_Host_i23 : Type v23} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (h_398 : Litex.In _value_i23 (Litex.N (M := M))) {_Host_i24 : Type v24} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (h_413 : Litex.In _value_i24 (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_396 h_398)) {_Host_i25 : Type v25} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (h_444 : Litex.In _value_i25 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398))) {_Host_i26 : Type v26} [_rep_i26 : Litex.Representation M _Host_i26] (_value_i26 : Litex.Obj (M := M) _Host_i26) (h_492 : Litex.In _value_i26 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))), (by
  let _object_h414 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_396 h_398)))
  have h_414 : Litex.In _value_i24 _object_h414 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i24 _value_i24 (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_396 h_398) _object_h414 (Litex.sameRefl _value_i24) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_396 h_398))) h_413)
        )
    )
  let _object_w32 := (let _litex_matrix_head := (Litex.conjugateTranspose _value_i24 _value_i22 _value_i23 h_396 h_398 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.C (M := M))) h_396 h_398)
    exact (show Litex.In _value_i24 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i33 : M.Value) (_raw_i34 : M.Value), M.mem _raw_i33 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))) → M.mem _raw_i34 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398))) → ((fun (_raw_i33 : M.Value) (_raw_i34 : M.Value) => True) _raw_i33 _raw_i34) → True := (by
          intro _raw_i33 _raw_i34 h_633 h_638 _
          let _value_i33 := Litex.semanticObject (M := M) _raw_i33 (M.member_isSet h_633)
          have h_633 : Litex.In _value_i33 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) := h_633
          have h_634 : Litex.In _value_i33 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i33 h_633).1
                )
            )
          have h_635 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i33 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i33 h_633).2.1
                )
            )
          have h_636 : Litex.Le _value_i33 _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i33 h_633).2.2
                )
            )
          have h_637 : Litex.In _value_i33 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i33 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_633)
                )
            )
          let _value_i34 := Litex.semanticObject (M := M) _raw_i34 (M.member_isSet h_638)
          have h_638 : Litex.In _value_i34 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) := h_638
          have h_639 : Litex.In _value_i34 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i34 h_638).1
                )
            )
          have h_640 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i34 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i34 h_638).2.1
                )
            )
          have h_641 : Litex.Le _value_i34 _value_i23 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i34 h_638).2.2
                )
            )
          have h_642 : Litex.In _value_i34 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i34 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_638)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i33 : M.Value) (_raw_i34 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i24 _value_i24 _object_h414 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h414
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_414))))));
  (let _litex_call_arg_0 := _value_i25;
  let _litex_call_arg_1 := _value_i26;
  Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.conjugateTransposeInRealFnSet _litex_matrix_head (by
    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i35 : M.Value) (_raw_i36 : M.Value), M.mem _raw_i35 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))) → M.mem _raw_i36 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398))) → ((fun (_raw_i35 : M.Value) (_raw_i36 : M.Value) => True) _raw_i35 _raw_i36) → True := (by
        intro _raw_i35 _raw_i36 h_656 h_661 _
        let _value_i35 := Litex.semanticObject (M := M) _raw_i35 (M.member_isSet h_656)
        have h_656 : Litex.In _value_i35 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) := h_656
        have h_657 : Litex.In _value_i35 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i35 h_656).1
              )
          )
        have h_658 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i35 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i35 h_656).2.1
              )
          )
        have h_659 : Litex.Le _value_i35 _value_i22 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i35 h_656).2.2
              )
          )
        have h_660 : Litex.In _value_i35 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i35 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_656)
              )
          )
        let _value_i36 := Litex.semanticObject (M := M) _raw_i36 (M.member_isSet h_661)
        have h_661 : Litex.In _value_i36 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) := h_661
        have h_662 : Litex.In _value_i36 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i36 h_661).1
              )
          )
        have h_663 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i36 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i36 h_661).2.1
              )
          )
        have h_664 : Litex.Le _value_i36 _value_i23 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i36 h_661).2.2
              )
          )
        have h_665 : Litex.In _value_i36 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i36 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_661)
              )
          )
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))] (by
      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)))
      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i35 : M.Value) (_raw_i36 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
    exact (Litex.inOfSame _value_i24 _value_i24 _object_h414 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h414
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_414))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398))
    exact h_444) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))
    exact h_492)), True.intro⟩)))
  exact (by
    let _atomic_wd_1_0 := _object_w32
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i22 _rep_i22 _value_i22 h_396 _Host_i23 _rep_i23 _value_i23 h_398 _Host_i24 _rep_i24 _value_i24 h_413 _Host_i25 _rep_i25 _value_i25 h_444 _Host_i26 _rep_i26 _value_i26 h_492
          have h_397 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i22 h_396)
                )
            )
          have h_399 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i23 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i23 h_398)
                )
            )
          let _object_h414 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_396 h_398)))
          have h_414 : Litex.In _value_i24 _object_h414 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i24 _value_i24 (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_396 h_398) _object_h414 (Litex.sameRefl _value_i24) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_396 h_398))) h_413)
                )
            )
          have h_445 : Litex.In _value_i25 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i25 h_444).1
                )
            )
          have h_446 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i25 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i25 h_444).2.1
                )
            )
          have h_447 : Litex.Le _value_i25 _value_i23 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i25 h_444).2.2
                )
            )
          have h_448 : Litex.In _value_i25 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i25 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_444)
                )
            )
          have h_493 : Litex.In _value_i26 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i26 h_492).1
                )
            )
          have h_494 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i26 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i26 h_492).2.1
                )
            )
          have h_495 : Litex.Le _value_i26 _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i26 h_492).2.2
                )
            )
          have h_496 : Litex.In _value_i26 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i26 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_492)
                )
            )
          let _object_w32 := (let _litex_matrix_head := (Litex.conjugateTranspose _value_i24 _value_i22 _value_i23 h_396 h_398 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.C (M := M))) h_396 h_398)
            exact (show Litex.In _value_i24 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i33 : M.Value) (_raw_i34 : M.Value), M.mem _raw_i33 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))) → M.mem _raw_i34 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398))) → ((fun (_raw_i33 : M.Value) (_raw_i34 : M.Value) => True) _raw_i33 _raw_i34) → True := (by
                  intro _raw_i33 _raw_i34 h_633 h_638 _
                  let _value_i33 := Litex.semanticObject (M := M) _raw_i33 (M.member_isSet h_633)
                  have h_633 : Litex.In _value_i33 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) := h_633
                  have h_634 : Litex.In _value_i33 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i33 h_633).1
                        )
                    )
                  have h_635 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i33 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i33 h_633).2.1
                        )
                    )
                  have h_636 : Litex.Le _value_i33 _value_i22 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i33 h_633).2.2
                        )
                    )
                  have h_637 : Litex.In _value_i33 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i33 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_633)
                        )
                    )
                  let _value_i34 := Litex.semanticObject (M := M) _raw_i34 (M.member_isSet h_638)
                  have h_638 : Litex.In _value_i34 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) := h_638
                  have h_639 : Litex.In _value_i34 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i34 h_638).1
                        )
                    )
                  have h_640 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i34 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i34 h_638).2.1
                        )
                    )
                  have h_641 : Litex.Le _value_i34 _value_i23 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i34 h_638).2.2
                        )
                    )
                  have h_642 : Litex.In _value_i34 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i34 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_638)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i33 : M.Value) (_raw_i34 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i24 _value_i24 _object_h414 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h414
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_414))))));
          (let _litex_call_arg_0 := _value_i25;
          let _litex_call_arg_1 := _value_i26;
          Litex.callOn (Litex.matrixTransposeSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .real) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.conjugateTransposeInRealFnSet _litex_matrix_head (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i35 : M.Value) (_raw_i36 : M.Value), M.mem _raw_i35 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))) → M.mem _raw_i36 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398))) → ((fun (_raw_i35 : M.Value) (_raw_i36 : M.Value) => True) _raw_i35 _raw_i36) → True := (by
                intro _raw_i35 _raw_i36 h_656 h_661 _
                let _value_i35 := Litex.semanticObject (M := M) _raw_i35 (M.member_isSet h_656)
                have h_656 : Litex.In _value_i35 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) := h_656
                have h_657 : Litex.In _value_i35 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i35 h_656).1
                      )
                  )
                have h_658 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i35 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i35 h_656).2.1
                      )
                  )
                have h_659 : Litex.Le _value_i35 _value_i22 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i35 h_656).2.2
                      )
                  )
                have h_660 : Litex.In _value_i35 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i35 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_656)
                      )
                  )
                let _value_i36 := Litex.semanticObject (M := M) _raw_i36 (M.member_isSet h_661)
                have h_661 : Litex.In _value_i36 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) := h_661
                have h_662 : Litex.In _value_i36 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i36 h_661).1
                      )
                  )
                have h_663 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i36 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i36 h_661).2.1
                      )
                  )
                have h_664 : Litex.Le _value_i36 _value_i23 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i36 h_661).2.2
                      )
                  )
                have h_665 : Litex.In _value_i36 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i36 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_661)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))] (by
              have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)))
              have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i35 : M.Value) (_raw_i36 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
            exact (Litex.inOfSame _value_i24 _value_i24 _object_h414 _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h414
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_414))) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398))
            exact h_444) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))
            exact h_492)), True.intro⟩)))
          have h_372 : (by
            let _atomic_wd_1_0 := _object_w32
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w32
                    exact (show Litex.In _atomic_wd_1_0 (Litex.R (M := M)) from (let _litex_matrix_signature := (Litex.matrixTransposeSignature ((_atomic_wd_1_0).val.function).val.rows ((_atomic_wd_1_0).val.function).val.cols .real); Litex.FunctionSemantics.call_mem _litex_matrix_signature.domain _litex_matrix_signature.output (Litex.denote (_atomic_wd_1_0).val.function) (Litex.denote (Litex.callArguments2 _value_i25 _value_i26)) (let _litex_matrix := (_atomic_wd_1_0).val.function; let _litex_matrix_signature := (Litex.matrixTransposeSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.conjugateTransposeInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i39 : M.Value) (_raw_i40 : M.Value), M.mem _raw_i39 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))) → M.mem _raw_i40 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398))) → ((fun (_raw_i39 : M.Value) (_raw_i40 : M.Value) => True) _raw_i39 _raw_i40) → True := (by
                          intro _raw_i39 _raw_i40 h_904 h_909 _
                          let _value_i39 := Litex.semanticObject (M := M) _raw_i39 (M.member_isSet h_904)
                          have h_904 : Litex.In _value_i39 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) := h_904
                          have h_905 : Litex.In _value_i39 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i39 h_904).1
                                )
                            )
                          have h_906 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i39 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i39 h_904).2.1
                                )
                            )
                          have h_907 : Litex.Le _value_i39 _value_i22 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i39 h_904).2.2
                                )
                            )
                          have h_908 : Litex.In _value_i39 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)) _value_i39 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_904)
                                )
                            )
                          let _value_i40 := Litex.semanticObject (M := M) _raw_i40 (M.member_isSet h_909)
                          have h_909 : Litex.In _value_i40 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) := h_909
                          have h_910 : Litex.In _value_i40 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i40 h_909).1
                                )
                            )
                          have h_911 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i40 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i40 h_909).2.1
                                )
                            )
                          have h_912 : Litex.Le _value_i40 _value_i23 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i40 h_909).2.2
                                )
                            )
                          have h_913 : Litex.In _value_i40 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)) _value_i40 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_909)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i39 : M.Value) (_raw_i40 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i24 _value_i24 _object_h414 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h414
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_414)))) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)))] (by
                      have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398)))
                      have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396)))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    ))) (fun (_litex_input : M.Value) => (fun (_raw_i41 : M.Value) (_raw_i42 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i25 _value_i26))).mpr ⟨(Litex.callArguments2_mem_cart _value_i25 _value_i26 (by
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_398))
                      exact h_444) (by
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_396))
                      exact h_492)), True.intro⟩))))
                )
            )
          exact h_372
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_conjugate_x5f_transpose_x5f_real_x2f_statement_x2e_lit
