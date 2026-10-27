import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_rank_x5f_membership_x2f_statement_x2e_lit

universe u v1 v2 v3 v6 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_21 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_36 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)), (by
  let _object_w5 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_19 h_21 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
    exact h_36))
  exact (by
    let _atomic_wd_1_0 := _object_w5
    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M)))
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
          let _object_h37 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)))
          have h_37 : Litex.In _value_i3 _object_h37 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21) _object_h37 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21))) h_36)
                )
            )
          let _object_w5 := (Litex.matrixRank _value_i3 _value_i1 _value_i2 h_19 h_21 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_19 h_21)
            exact h_36))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w5
            exact Litex.In _atomic_wd_1_0 (Litex.N (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    exact (Litex.matrixRankInN _atomic_wd_1_0))
                )
            )
          have h_76 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _object_w5 h_1)
                )
            )
          exact h_1
        )
      )
  )

theorem h_78 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_95 : Litex.In _value_i6 (Litex.N (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_97 : Litex.In _value_i7 (Litex.N (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_112 : Litex.In _value_i8 (Litex.matrixSet (Litex.R (M := M)) _value_i6 _value_i7 (Litex.isSet (Litex.R (M := M))) h_95 h_97)), (by
  let _object_h113 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i6 _value_i7 (Litex.isSet (Litex.R (M := M))) h_95 h_97)))
  have h_113 : Litex.In _value_i8 _object_h113 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i8 _value_i8 (Litex.matrixSet (Litex.R (M := M)) _value_i6 _value_i7 (Litex.isSet (Litex.R (M := M))) h_95 h_97) _object_h113 (Litex.sameRefl _value_i8) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i6 _value_i7 (Litex.isSet (Litex.R (M := M))) h_95 h_97))) h_112)
        )
    )
  let _object_w20 := (Litex.matrixRank _value_i8 _value_i6 _value_i7 h_95 h_97 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i6 _value_i7 (Litex.isSet (Litex.C (M := M))) h_95 h_97)
    exact (show Litex.In _value_i8 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i15 : M.Value) (_raw_i16 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95))) → M.mem _raw_i16 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97))) → ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) _raw_i15 _raw_i16) → True := (by
          intro _raw_i15 _raw_i16 h_316 h_321 _
          let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_316)
          have h_316 : Litex.In _value_i15 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95)) := h_316
          have h_317 : Litex.In _value_i15 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95)) _value_i15 h_316).1
                )
            )
          have h_318 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95)) _value_i15 h_316).2.1
                )
            )
          have h_319 : Litex.Le _value_i15 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95)) _value_i15 h_316).2.2
                )
            )
          have h_320 : Litex.In _value_i15 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95)) _value_i15 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_316)
                )
            )
          let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_321)
          have h_321 : Litex.In _value_i16 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)) := h_321
          have h_322 : Litex.In _value_i16 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)) _value_i16 h_321).1
                )
            )
          have h_323 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i16 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)) _value_i16 h_321).2.1
                )
            )
          have h_324 : Litex.Le _value_i16 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)) _value_i16 h_321).2.2
                )
            )
          have h_325 : Litex.In _value_i16 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)) _value_i16 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_321)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i8 _value_i8 _object_h113 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h113
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_113))))))
  exact (by
    let _atomic_wd_1_0 := _object_w20
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_95 _Host_i7 _rep_i7 _value_i7 h_97 _Host_i8 _rep_i8 _value_i8 h_112
          have h_96 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i6 h_95)
                )
            )
          have h_98 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i7 h_97)
                )
            )
          let _object_h113 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i6 _value_i7 (Litex.isSet (Litex.R (M := M))) h_95 h_97)))
          have h_113 : Litex.In _value_i8 _object_h113 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i8 _value_i8 (Litex.matrixSet (Litex.R (M := M)) _value_i6 _value_i7 (Litex.isSet (Litex.R (M := M))) h_95 h_97) _object_h113 (Litex.sameRefl _value_i8) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i6 _value_i7 (Litex.isSet (Litex.R (M := M))) h_95 h_97))) h_112)
                )
            )
          let _object_w20 := (Litex.matrixRank _value_i8 _value_i6 _value_i7 h_95 h_97 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i6 _value_i7 (Litex.isSet (Litex.C (M := M))) h_95 h_97)
            exact (show Litex.In _value_i8 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i15 : M.Value) (_raw_i16 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95))) → M.mem _raw_i16 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97))) → ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) _raw_i15 _raw_i16) → True := (by
                  intro _raw_i15 _raw_i16 h_316 h_321 _
                  let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_316)
                  have h_316 : Litex.In _value_i15 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95)) := h_316
                  have h_317 : Litex.In _value_i15 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95)) _value_i15 h_316).1
                        )
                    )
                  have h_318 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i15 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95)) _value_i15 h_316).2.1
                        )
                    )
                  have h_319 : Litex.Le _value_i15 _value_i6 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95)) _value_i15 h_316).2.2
                        )
                    )
                  have h_320 : Litex.In _value_i15 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95)) _value_i15 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_316)
                        )
                    )
                  let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_321)
                  have h_321 : Litex.In _value_i16 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)) := h_321
                  have h_322 : Litex.In _value_i16 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)) _value_i16 h_321).1
                        )
                    )
                  have h_323 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i16 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)) _value_i16 h_321).2.1
                        )
                    )
                  have h_324 : Litex.Le _value_i16 _value_i7 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)) _value_i16 h_321).2.2
                        )
                    )
                  have h_325 : Litex.In _value_i16 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)) _value_i16 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_321)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_95)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 h_97)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i8 _value_i8 _object_h113 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h113
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_113))))))
          have h_77 : (by
            let _atomic_wd_1_0 := _object_w20
            exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w20
                    exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.matrixRankInN _atomic_wd_1_0)))
                )
            )
          exact h_77
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_rank_x5f_membership_x2f_statement_x2e_lit
