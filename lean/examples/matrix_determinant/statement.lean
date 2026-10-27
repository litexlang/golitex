import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_determinant_x2f_statement_x2e_lit

universe u v1 v2 v5 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_32 : Litex.In _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)), (by
  let _object_w5 := (Litex.matrixDeterminant _value_i2 _value_i1 h_19 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)
    exact h_32))
  exact (by
    let _atomic_wd_1_0 := _object_w5
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_19 _Host_i2 _rep_i2 _value_i2 h_32
          have h_20 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_19)
                )
            )
          let _object_h33 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)))
          have h_33 : Litex.In _value_i2 _object_h33 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19) _object_h33 (Litex.sameRefl _value_i2) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19))) h_32)
                )
            )
          let _object_w5 := (Litex.matrixDeterminant _value_i2 _value_i1 h_19 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)
            exact h_32))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w5
            exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    exact (Litex.matrixDeterminantInC _atomic_wd_1_0))
                )
            )
          exact h_1
        )
      )
  )

theorem h_60 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_77 : Litex.In _value_i5 (Litex.N (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_90 : Litex.In _value_i6 (Litex.matrixSet (Litex.R (M := M)) _value_i5 _value_i5 (Litex.isSet (Litex.R (M := M))) h_77 h_77)), (by
  let _object_h91 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i5 _value_i5 (Litex.isSet (Litex.R (M := M))) h_77 h_77)))
  have h_91 : Litex.In _value_i6 _object_h91 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i6 _value_i6 (Litex.matrixSet (Litex.R (M := M)) _value_i5 _value_i5 (Litex.isSet (Litex.R (M := M))) h_77 h_77) _object_h91 (Litex.sameRefl _value_i6) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i5 _value_i5 (Litex.isSet (Litex.R (M := M))) h_77 h_77))) h_90)
        )
    )
  let _object_w23 := (Litex.matrixDeterminant _value_i6 _value_i5 h_77 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i5 _value_i5 (Litex.isSet (Litex.C (M := M))) h_77 h_77)
    exact (show Litex.In _value_i6 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i13 : M.Value) (_raw_i14 : M.Value), M.mem _raw_i13 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77))) → M.mem _raw_i14 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77))) → ((fun (_raw_i13 : M.Value) (_raw_i14 : M.Value) => True) _raw_i13 _raw_i14) → True := (by
          intro _raw_i13 _raw_i14 h_255 h_260 _
          let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_255)
          have h_255 : Litex.In _value_i13 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) := h_255
          have h_256 : Litex.In _value_i13 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i13 h_255).1
                )
            )
          have h_257 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i13 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i13 h_255).2.1
                )
            )
          have h_258 : Litex.Le _value_i13 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i13 h_255).2.2
                )
            )
          have h_259 : Litex.In _value_i13 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i13 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_255)
                )
            )
          let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_260)
          have h_260 : Litex.In _value_i14 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) := h_260
          have h_261 : Litex.In _value_i14 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i14 h_260).1
                )
            )
          have h_262 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i14 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i14 h_260).2.1
                )
            )
          have h_263 : Litex.Le _value_i14 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i14 h_260).2.2
                )
            )
          have h_264 : Litex.In _value_i14 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i14 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_260)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) (_raw_i14 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i6 _value_i6 _object_h91 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h91
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_91))))))
  exact (by
    let _atomic_wd_1_0 := _object_w23
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_77 _Host_i6 _rep_i6 _value_i6 h_90
          have h_78 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i5 h_77)
                )
            )
          let _object_h91 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i5 _value_i5 (Litex.isSet (Litex.R (M := M))) h_77 h_77)))
          have h_91 : Litex.In _value_i6 _object_h91 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i6 _value_i6 (Litex.matrixSet (Litex.R (M := M)) _value_i5 _value_i5 (Litex.isSet (Litex.R (M := M))) h_77 h_77) _object_h91 (Litex.sameRefl _value_i6) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i5 _value_i5 (Litex.isSet (Litex.R (M := M))) h_77 h_77))) h_90)
                )
            )
          let _object_w23 := (Litex.matrixDeterminant _value_i6 _value_i5 h_77 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i5 _value_i5 (Litex.isSet (Litex.C (M := M))) h_77 h_77)
            exact (show Litex.In _value_i6 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i13 : M.Value) (_raw_i14 : M.Value), M.mem _raw_i13 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77))) → M.mem _raw_i14 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77))) → ((fun (_raw_i13 : M.Value) (_raw_i14 : M.Value) => True) _raw_i13 _raw_i14) → True := (by
                  intro _raw_i13 _raw_i14 h_255 h_260 _
                  let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_255)
                  have h_255 : Litex.In _value_i13 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) := h_255
                  have h_256 : Litex.In _value_i13 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i13 h_255).1
                        )
                    )
                  have h_257 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i13 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i13 h_255).2.1
                        )
                    )
                  have h_258 : Litex.Le _value_i13 _value_i5 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i13 h_255).2.2
                        )
                    )
                  have h_259 : Litex.In _value_i13 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i13 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_255)
                        )
                    )
                  let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_260)
                  have h_260 : Litex.In _value_i14 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) := h_260
                  have h_261 : Litex.In _value_i14 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i14 h_260).1
                        )
                    )
                  have h_262 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i14 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i14 h_260).2.1
                        )
                    )
                  have h_263 : Litex.Le _value_i14 _value_i5 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i14 h_260).2.2
                        )
                    )
                  have h_264 : Litex.In _value_i14 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i14 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_260)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) (_raw_i14 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i6 _value_i6 _object_h91 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h91
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_91))))))
          have h_59 : (by
            let _atomic_wd_1_0 := _object_w23
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w23
                    exact (show Litex.In _atomic_wd_1_0 (Litex.R (M := M)) from (Litex.matrixDeterminantInR _atomic_wd_1_0 (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i15 : M.Value) (_raw_i16 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77))) → M.mem _raw_i16 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77))) → ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) _raw_i15 _raw_i16) → True := (by
                          intro _raw_i15 _raw_i16 h_389 h_394 _
                          let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_389)
                          have h_389 : Litex.In _value_i15 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) := h_389
                          have h_390 : Litex.In _value_i15 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i15 h_389).1
                                )
                            )
                          have h_391 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i15 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i15 h_389).2.1
                                )
                            )
                          have h_392 : Litex.Le _value_i15 _value_i5 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i15 h_389).2.2
                                )
                            )
                          have h_393 : Litex.In _value_i15 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i15 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_389)
                                )
                            )
                          let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_394)
                          have h_394 : Litex.In _value_i16 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) := h_394
                          have h_395 : Litex.In _value_i16 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i16 h_394).1
                                )
                            )
                          have h_396 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i16 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i16 h_394).2.1
                                )
                            )
                          have h_397 : Litex.Le _value_i16 _value_i5 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i16 h_394).2.2
                                )
                            )
                          have h_398 : Litex.In _value_i16 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)) _value_i16 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_394)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i5 h_77)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i6 _value_i6 _object_h91 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h91
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_91)))))
                )
            )
          exact h_59
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_determinant_x2f_statement_x2e_lit
