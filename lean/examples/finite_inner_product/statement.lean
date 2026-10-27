import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_inner_x5f_product_x2f_statement_x2e_lit

universe u v1 v2 v3 v6 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_18 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_26 : Litex.In _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_28 : Litex.In _value_i3 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)), (by
  let _object_w6 := (Litex.finiteInnerProduct _value_i2 _value_i3 _value_i1 h_18 (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
    exact h_26) (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
    exact h_28))
  exact (by
    let _atomic_wd_1_0 := _object_w6
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_18 _Host_i2 _rep_i2 _value_i2 h_26 _Host_i3 _rep_i3 _value_i3 h_28
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
          let _object_h29 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)))
          have h_29 : Litex.In _value_i3 _object_h29 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18) _object_h29 (Litex.sameRefl _value_i3) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)) h_28)
                )
            )
          let _object_w6 := (Litex.finiteInnerProduct _value_i2 _value_i3 _value_i1 h_18 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
            exact h_26) (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
            exact h_28))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w6
            exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w6
                    exact (Litex.finiteInnerProductInC _atomic_wd_1_0))
                )
            )
          exact h_1
        )
      )
  )

theorem h_75 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_91 : Litex.In _value_i6 (Litex.N (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_99 : Litex.In _value_i7 (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91)) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_101 : Litex.In _value_i8 (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91)), (by
  let _object_h100 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91)))
  have h_100 : Litex.In _value_i7 _object_h100 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i7 _value_i7 (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91) _object_h100 (Litex.sameRefl _value_i7) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91)) h_99)
        )
    )
  let _object_h102 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91)))
  have h_102 : Litex.In _value_i8 _object_h102 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i8 _value_i8 (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91) _object_h102 (Litex.sameRefl _value_i8) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91)) h_101)
        )
    )
  let _object_w41 := (Litex.finiteInnerProduct _value_i7 _value_i8 _value_i6 h_91 (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i6 (Litex.isSet (Litex.C (M := M))) h_91)
    exact (by
      let _membership_function := _value_i7
      let _membership_target := (let _checked_header : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) → ((fun (_raw_i12 : M.Value) => True) _raw_i12) → True := (by
          intro _raw_i12 h_176 _
          let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_176)
          have h_176 : Litex.In _value_i12 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) := h_176
          have h_177 : Litex.In _value_i12 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 h_176).1
                )
            )
          have h_178 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i12 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 h_176).2.1
                )
            )
          have h_179 : Litex.Le _value_i12 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 h_176).2.2
                )
            )
          have h_180 : Litex.In _value_i12 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_176)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) => True) _litex_input)))
      have h_181 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_427 : Litex.In _value_i12 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))), (by
        let _object_w21 := (let _litex_call_arg_0 := _value_i12;
        Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i7 _litex_call_arg_0 h_100 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))
          exact h_427) True.intro)
        exact (by
          let _atomic_wd_2_0 := _object_w21
          exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
      ) := (by
        intro _Host_i12 _rep_i12 _value_i12 h_427
        have h_428 : Litex.In _value_i12 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 h_427).1
              )
          )
        have h_429 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i12 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 h_427).2.1
              )
          )
        have h_430 : Litex.Le _value_i12 _value_i6 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 h_427).2.2
              )
          )
        have h_431 : Litex.In _value_i12 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_427)
              )
          )
        let _object_w21 := (let _litex_call_arg_0 := _value_i12;
        Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i7 _litex_call_arg_0 h_100 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))
          exact h_427) True.intro)
        have h_182 : (by
          let _atomic_wd_2_0 := _object_w21
          exact Litex.In _atomic_wd_2_0 (Litex.C (M := M))) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  let _atomic_wd_2_0 := _object_w21
                  exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callOnInOutput _atomic_wd_2_0)))
              )
          )
        exact h_182
      )
      exact (by
        let _source_signature := (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input))
        have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame _value_i7 _value_i7 (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91))) h_99)
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
        exact h_181 _arg_0 _member_0))) (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i6 (Litex.isSet (Litex.C (M := M))) h_91)
    exact (by
      let _membership_function := _value_i8
      let _membership_target := (let _checked_header : ∀ (_raw_i15 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) → ((fun (_raw_i15 : M.Value) => True) _raw_i15) → True := (by
          intro _raw_i15 h_680 _
          let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_680)
          have h_680 : Litex.In _value_i15 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) := h_680
          have h_681 : Litex.In _value_i15 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 h_680).1
                )
            )
          have h_682 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 h_680).2.1
                )
            )
          have h_683 : Litex.Le _value_i15 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 h_680).2.2
                )
            )
          have h_684 : Litex.In _value_i15 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_680)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input)))
      have h_685 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_931 : Litex.In _value_i15 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))), (by
        let _object_w31 := (let _litex_call_arg_0 := _value_i15;
        Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_102 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))
          exact h_931) True.intro)
        exact (by
          let _atomic_wd_2_0 := _object_w31
          exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
      ) := (by
        intro _Host_i15 _rep_i15 _value_i15 h_931
        have h_932 : Litex.In _value_i15 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 h_931).1
              )
          )
        have h_933 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i15 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 h_931).2.1
              )
          )
        have h_934 : Litex.Le _value_i15 _value_i6 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 h_931).2.2
              )
          )
        have h_935 : Litex.In _value_i15 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_931)
              )
          )
        let _object_w31 := (let _litex_call_arg_0 := _value_i15;
        Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_102 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))
          exact h_931) True.intro)
        have h_686 : (by
          let _atomic_wd_2_0 := _object_w31
          exact Litex.In _atomic_wd_2_0 (Litex.C (M := M))) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  let _atomic_wd_2_0 := _object_w31
                  exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callOnInOutput _atomic_wd_2_0)))
              )
          )
        exact h_686
      )
      exact (by
        let _source_signature := (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input))
        have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame _value_i8 _value_i8 (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91))) h_101)
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
        exact h_685 _arg_0 _member_0))))
  exact (by
    let _atomic_wd_1_0 := _object_w41
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_91 _Host_i7 _rep_i7 _value_i7 h_99 _Host_i8 _rep_i8 _value_i8 h_101
          have h_92 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i6 h_91)
                )
            )
          let _object_h100 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91)))
          have h_100 : Litex.In _value_i7 _object_h100 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i7 _value_i7 (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91) _object_h100 (Litex.sameRefl _value_i7) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91)) h_99)
                )
            )
          let _object_h102 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91)))
          have h_102 : Litex.In _value_i8 _object_h102 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i8 _value_i8 (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91) _object_h102 (Litex.sameRefl _value_i8) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91)) h_101)
                )
            )
          let _object_w41 := (Litex.finiteInnerProduct _value_i7 _value_i8 _value_i6 h_91 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i6 (Litex.isSet (Litex.C (M := M))) h_91)
            exact (by
              let _membership_function := _value_i7
              let _membership_target := (let _checked_header : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) → ((fun (_raw_i12 : M.Value) => True) _raw_i12) → True := (by
                  intro _raw_i12 h_176 _
                  let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_176)
                  have h_176 : Litex.In _value_i12 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) := h_176
                  have h_177 : Litex.In _value_i12 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 h_176).1
                        )
                    )
                  have h_178 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i12 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 h_176).2.1
                        )
                    )
                  have h_179 : Litex.Le _value_i12 _value_i6 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 h_176).2.2
                        )
                    )
                  have h_180 : Litex.In _value_i12 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_176)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) => True) _litex_input)))
              have h_181 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_427 : Litex.In _value_i12 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))), (by
                let _object_w21 := (let _litex_call_arg_0 := _value_i12;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i7 _litex_call_arg_0 h_100 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))
                  exact h_427) True.intro)
                exact (by
                  let _atomic_wd_2_0 := _object_w21
                  exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
              ) := (by
                intro _Host_i12 _rep_i12 _value_i12 h_427
                have h_428 : Litex.In _value_i12 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 h_427).1
                      )
                  )
                have h_429 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i12 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 h_427).2.1
                      )
                  )
                have h_430 : Litex.Le _value_i12 _value_i6 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 h_427).2.2
                      )
                  )
                have h_431 : Litex.In _value_i12 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i12 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_427)
                      )
                  )
                let _object_w21 := (let _litex_call_arg_0 := _value_i12;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i7 _litex_call_arg_0 h_100 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))
                  exact h_427) True.intro)
                have h_182 : (by
                  let _atomic_wd_2_0 := _object_w21
                  exact Litex.In _atomic_wd_2_0 (Litex.C (M := M))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_2_0 := _object_w21
                          exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callOnInOutput _atomic_wd_2_0)))
                      )
                  )
                exact h_182
              )
              exact (by
                let _source_signature := (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input))
                have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame _value_i7 _value_i7 (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91))) h_99)
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
                exact h_181 _arg_0 _member_0))) (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i6 (Litex.isSet (Litex.C (M := M))) h_91)
            exact (by
              let _membership_function := _value_i8
              let _membership_target := (let _checked_header : ∀ (_raw_i15 : M.Value), M.mem _raw_i15 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) → ((fun (_raw_i15 : M.Value) => True) _raw_i15) → True := (by
                  intro _raw_i15 h_680 _
                  let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_680)
                  have h_680 : Litex.In _value_i15 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) := h_680
                  have h_681 : Litex.In _value_i15 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 h_680).1
                        )
                    )
                  have h_682 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i15 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 h_680).2.1
                        )
                    )
                  have h_683 : Litex.Le _value_i15 _value_i6 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 h_680).2.2
                        )
                    )
                  have h_684 : Litex.In _value_i15 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_680)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input)))
              have h_685 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_931 : Litex.In _value_i15 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))), (by
                let _object_w31 := (let _litex_call_arg_0 := _value_i15;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_102 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))
                  exact h_931) True.intro)
                exact (by
                  let _atomic_wd_2_0 := _object_w31
                  exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
              ) := (by
                intro _Host_i15 _rep_i15 _value_i15 h_931
                have h_932 : Litex.In _value_i15 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 h_931).1
                      )
                  )
                have h_933 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i15 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 h_931).2.1
                      )
                  )
                have h_934 : Litex.Le _value_i15 _value_i6 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 h_931).2.2
                      )
                  )
                have h_935 : Litex.In _value_i15 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i15 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_931)
                      )
                  )
                let _object_w31 := (let _litex_call_arg_0 := _value_i15;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_102 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))
                  exact h_931) True.intro)
                have h_686 : (by
                  let _atomic_wd_2_0 := _object_w31
                  exact Litex.In _atomic_wd_2_0 (Litex.C (M := M))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_2_0 := _object_w31
                          exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callOnInOutput _atomic_wd_2_0)))
                      )
                  )
                exact h_686
              )
              exact (by
                let _source_signature := (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input))
                have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame _value_i8 _value_i8 (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i6 (Litex.isSet (Litex.R (M := M))) h_91))) h_101)
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
                exact h_685 _arg_0 _member_0))))
          have h_74 : (by
            let _atomic_wd_1_0 := _object_w41
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w41
                    exact (show Litex.In _atomic_wd_1_0 (Litex.R (M := M)) from (Litex.finiteInnerProductInR _atomic_wd_1_0 (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i17 : M.Value), M.mem _raw_i17 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) → ((fun (_raw_i17 : M.Value) => True) _raw_i17) → True := (by
                          intro _raw_i17 h_1253 _
                          let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_1253)
                          have h_1253 : Litex.In _value_i17 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) := h_1253
                          have h_1254 : Litex.In _value_i17 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i17 h_1253).1
                                )
                            )
                          have h_1255 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i17 h_1253).2.1
                                )
                            )
                          have h_1256 : Litex.Le _value_i17 _value_i6 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i17 h_1253).2.2
                                )
                            )
                          have h_1257 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1253)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input)))
                      exact (Litex.inOfSame _value_i7 _value_i7 _object_h100 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h100
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_100)) (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i18 : M.Value), M.mem _raw_i18 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) → ((fun (_raw_i18 : M.Value) => True) _raw_i18) → True := (by
                          intro _raw_i18 h_1302 _
                          let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_1302)
                          have h_1302 : Litex.In _value_i18 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) := h_1302
                          have h_1303 : Litex.In _value_i18 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i18 h_1302).1
                                )
                            )
                          have h_1304 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i18 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i18 h_1302).2.1
                                )
                            )
                          have h_1305 : Litex.Le _value_i18 _value_i6 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i18 h_1302).2.2
                                )
                            )
                          have h_1306 : Litex.In _value_i18 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91)) _value_i18 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1302)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i6 h_91))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input)))
                      exact (Litex.inOfSame _value_i8 _value_i8 _object_h102 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h102
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_102)))))
                )
            )
          exact h_74
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_inner_x5f_product_x2f_statement_x2e_lit
