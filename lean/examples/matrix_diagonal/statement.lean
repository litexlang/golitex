import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_diagonal_x2f_statement_x2e_lit

universe u v1 v2 v13 v14
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_18 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_26 : Litex.In _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)), (by
  let _object_w9 := (Litex.matrixDiagonal _value_i2 _value_i1 h_18 (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
    exact h_26))
  let _object_w10 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_18 h_18)
  exact (by
    let _atomic_wd_1_0 := _object_w9
    let _atomic_wd_1_1 := _object_w10
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_18 _Host_i2 _rep_i2 _value_i2 h_26
          have h_19 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_18)
                )
            )
          let _object_h27 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)))
          have h_27 : Litex.In _value_i2 _object_h27 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18) _object_h27 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)) h_26)
                )
            )
          let _object_w9 := (Litex.matrixDiagonal _value_i2 _value_i1 h_18 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
            exact h_26))
          let _object_w10 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_18 h_18)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w9
            let _atomic_wd_1_1 := _object_w10
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    let _atomic_wd_1_1 := _object_w10
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.order (_litex_matrix).val.order .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixDiagonalInFnSet _litex_matrix))))
                )
            )
          let _object_h113 := (Litex.fnSet (Litex.matrixSignature _object_w10))
          have h_113 : Litex.In _object_w9 _object_h113 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w9 _object_w9 _object_w10 _object_h113 (Litex.sameRefl _object_w9) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet _object_w10)) h_1)
                )
            )
          exact h_1
        )
      )
  )

theorem h_115 : ∀ {_Host_i13 : Type v13} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_131 : Litex.In _value_i13 (Litex.N (M := M))) {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_139 : Litex.In _value_i14 (Litex.finiteSeq (Litex.R (M := M)) _value_i13 (Litex.isSet (Litex.R (M := M))) h_131)), (by
  let _object_h140 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) _value_i13 (Litex.isSet (Litex.R (M := M))) h_131)))
  have h_140 : Litex.In _value_i14 _object_h140 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i14 _value_i14 (Litex.finiteSeq (Litex.R (M := M)) _value_i13 (Litex.isSet (Litex.R (M := M))) h_131) _object_h140 (Litex.sameRefl _value_i14) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i13 (Litex.isSet (Litex.R (M := M))) h_131)) h_139)
        )
    )
  let _object_w30 := (Litex.matrixDiagonal _value_i14 _value_i13 h_131 (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i13 (Litex.isSet (Litex.C (M := M))) h_131)
    exact (by
      let _membership_function := _value_i14
      let _membership_target := (let _checked_header : ∀ (_raw_i17 : M.Value), M.mem _raw_i17 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) → ((fun (_raw_i17 : M.Value) => True) _raw_i17) → True := (by
          intro _raw_i17 h_196 _
          let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_196)
          have h_196 : Litex.In _value_i17 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) := h_196
          have h_197 : Litex.In _value_i17 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 h_196).1
                )
            )
          have h_198 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 h_196).2.1
                )
            )
          have h_199 : Litex.Le _value_i17 _value_i13 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 h_196).2.2
                )
            )
          have h_200 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_196)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input)))
      have h_201 : ∀ {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_377 : Litex.In _value_i17 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))), (by
        let _object_w24 := (let _litex_call_arg_0 := _value_i17;
        Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input) _value_i14 _litex_call_arg_0 h_140 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))
          exact h_377) True.intro)
        exact (by
          let _atomic_wd_2_0 := _object_w24
          exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
      ) := (by
        intro _Host_i17 _rep_i17 _value_i17 h_377
        have h_378 : Litex.In _value_i17 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 h_377).1
              )
          )
        have h_379 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 h_377).2.1
              )
          )
        have h_380 : Litex.Le _value_i17 _value_i13 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 h_377).2.2
              )
          )
        have h_381 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_377)
              )
          )
        let _object_w24 := (let _litex_call_arg_0 := _value_i17;
        Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input) _value_i14 _litex_call_arg_0 h_140 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))
          exact h_377) True.intro)
        have h_202 : (by
          let _atomic_wd_2_0 := _object_w24
          exact Litex.In _atomic_wd_2_0 (Litex.C (M := M))) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  let _atomic_wd_2_0 := _object_w24
                  exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callOnInOutput _atomic_wd_2_0)))
              )
          )
        exact h_202
      )
      exact (by
        let _source_signature := (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))
        have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame _value_i14 _value_i14 (Litex.finiteSeq (Litex.R (M := M)) _value_i13 (Litex.isSet (Litex.R (M := M))) h_131) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i13 (Litex.isSet (Litex.R (M := M))) h_131))) h_139)
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
        exact h_201 _arg_0 _member_0))))
  let _object_w31 := (Litex.matrixSet (Litex.R (M := M)) _value_i13 _value_i13 (Litex.isSet (Litex.R (M := M))) h_131 h_131)
  exact (by
    let _atomic_wd_1_0 := _object_w30
    let _atomic_wd_1_1 := _object_w31
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i13 _rep_i13 _value_i13 h_131 _Host_i14 _rep_i14 _value_i14 h_139
          have h_132 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i13 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i13 h_131)
                )
            )
          let _object_h140 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) _value_i13 (Litex.isSet (Litex.R (M := M))) h_131)))
          have h_140 : Litex.In _value_i14 _object_h140 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i14 _value_i14 (Litex.finiteSeq (Litex.R (M := M)) _value_i13 (Litex.isSet (Litex.R (M := M))) h_131) _object_h140 (Litex.sameRefl _value_i14) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i13 (Litex.isSet (Litex.R (M := M))) h_131)) h_139)
                )
            )
          let _object_w30 := (Litex.matrixDiagonal _value_i14 _value_i13 h_131 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i13 (Litex.isSet (Litex.C (M := M))) h_131)
            exact (by
              let _membership_function := _value_i14
              let _membership_target := (let _checked_header : ∀ (_raw_i17 : M.Value), M.mem _raw_i17 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) → ((fun (_raw_i17 : M.Value) => True) _raw_i17) → True := (by
                  intro _raw_i17 h_196 _
                  let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_196)
                  have h_196 : Litex.In _value_i17 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) := h_196
                  have h_197 : Litex.In _value_i17 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 h_196).1
                        )
                    )
                  have h_198 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 h_196).2.1
                        )
                    )
                  have h_199 : Litex.Le _value_i17 _value_i13 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 h_196).2.2
                        )
                    )
                  have h_200 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_196)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input)))
              have h_201 : ∀ {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_377 : Litex.In _value_i17 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))), (by
                let _object_w24 := (let _litex_call_arg_0 := _value_i17;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input) _value_i14 _litex_call_arg_0 h_140 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))
                  exact h_377) True.intro)
                exact (by
                  let _atomic_wd_2_0 := _object_w24
                  exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
              ) := (by
                intro _Host_i17 _rep_i17 _value_i17 h_377
                have h_378 : Litex.In _value_i17 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 h_377).1
                      )
                  )
                have h_379 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 h_377).2.1
                      )
                  )
                have h_380 : Litex.Le _value_i17 _value_i13 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 h_377).2.2
                      )
                  )
                have h_381 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_377)
                      )
                  )
                let _object_w24 := (let _litex_call_arg_0 := _value_i17;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input) _value_i14 _litex_call_arg_0 h_140 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))
                  exact h_377) True.intro)
                have h_202 : (by
                  let _atomic_wd_2_0 := _object_w24
                  exact Litex.In _atomic_wd_2_0 (Litex.C (M := M))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_2_0 := _object_w24
                          exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callOnInOutput _atomic_wd_2_0)))
                      )
                  )
                exact h_202
              )
              exact (by
                let _source_signature := (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))
                have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame _value_i14 _value_i14 (Litex.finiteSeq (Litex.R (M := M)) _value_i13 (Litex.isSet (Litex.R (M := M))) h_131) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i13 (Litex.isSet (Litex.R (M := M))) h_131))) h_139)
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
                exact h_201 _arg_0 _member_0))))
          let _object_w31 := (Litex.matrixSet (Litex.R (M := M)) _value_i13 _value_i13 (Litex.isSet (Litex.R (M := M))) h_131 h_131)
          have h_114 : (by
            let _atomic_wd_1_0 := _object_w30
            let _atomic_wd_1_1 := _object_w31
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w30
                    let _atomic_wd_1_1 := _object_w31
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.order (_litex_matrix).val.order .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixDiagonalInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i23 : M.Value), M.mem _raw_i23 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) → ((fun (_raw_i23 : M.Value) => True) _raw_i23) → True := (by
                          intro _raw_i23 h_569 _
                          let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_569)
                          have h_569 : Litex.In _value_i23 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) := h_569
                          have h_570 : Litex.In _value_i23 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i23 h_569).1
                                )
                            )
                          have h_571 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i23 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i23 h_569).2.1
                                )
                            )
                          have h_572 : Litex.Le _value_i23 _value_i13 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i23 h_569).2.2
                                )
                            )
                          have h_573 : Litex.In _value_i23 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131)) _value_i23 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_569)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i13 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i13 h_131))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) => True) _litex_input)))
                      exact (Litex.inOfSame _value_i14 _value_i14 _object_h140 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h140
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_140))))))
                )
            )
          let _object_h584 := (Litex.fnSet (Litex.matrixSignature _object_w31))
          have h_584 : Litex.In _object_w30 _object_h584 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w30 _object_w30 _object_w31 _object_h584 (Litex.sameRefl _object_w30) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet _object_w31)) h_114)
                )
            )
          exact h_114
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_diagonal_x2f_statement_x2e_lit
