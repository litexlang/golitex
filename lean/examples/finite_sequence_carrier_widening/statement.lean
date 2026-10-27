import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_sequence_x5f_carrier_x5f_widening_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_18 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_26 : Litex.In _value_i2 (Litex.finiteSeq (Litex.R (M := M)) _value_i1 (Litex.isSet (Litex.R (M := M))) h_18)), (by
  let _object_w15 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
  exact (by
    let _atomic_wd_1_1 := _object_w15
    exact Litex.In _value_i2 _atomic_wd_1_1)
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
          let _object_h27 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) _value_i1 (Litex.isSet (Litex.R (M := M))) h_18)))
          have h_27 : Litex.In _value_i2 _object_h27 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.R (M := M)) _value_i1 (Litex.isSet (Litex.R (M := M))) h_18) _object_h27 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i1 (Litex.isSet (Litex.R (M := M))) h_18)) h_26)
                )
            )
          let _object_w15 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_18)
          have h_1 : (by
            let _atomic_wd_1_1 := _object_w15
            exact Litex.In _value_i2 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w15
                    exact (by
                      let _membership_function := _value_i2
                      let _membership_target := (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → True := (by
                          intro _raw_i5 h_77 _
                          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_77)
                          have h_77 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18)) := h_77
                          have h_78 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18)) _value_i5 h_77).1
                                )
                            )
                          have h_79 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18)) _value_i5 h_77).2.1
                                )
                            )
                          have h_80 : Litex.Le _value_i5 _value_i1 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18)) _value_i5 h_77).2.2
                                )
                            )
                          have h_81 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_77)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)))
                      have h_82 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_258 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))), (by
                        let _object_w13 := (let _litex_call_arg_0 := _value_i5;
                        Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
                          exact h_258) True.intro)
                        exact (by
                          let _atomic_wd_2_0 := _object_w13
                          exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
                      ) := (by
                        intro _Host_i5 _rep_i5 _value_i5 h_258
                        have h_259 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18)) _value_i5 h_258).1
                              )
                          )
                        have h_260 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18)) _value_i5 h_258).2.1
                              )
                          )
                        have h_261 : Litex.Le _value_i5 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18)) _value_i5 h_258).2.2
                              )
                          )
                        have h_262 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_258)
                              )
                          )
                        let _object_w13 := (let _litex_call_arg_0 := _value_i5;
                        Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_27 (by
                          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))
                          exact h_258) True.intro)
                        have h_83 : (by
                          let _atomic_wd_2_0 := _object_w13
                          exact Litex.In _atomic_wd_2_0 (Litex.C (M := M))) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  let _atomic_wd_2_0 := _object_w13
                                  exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callOnInOutput _atomic_wd_2_0)))
                              )
                          )
                        exact h_83
                      )
                      exact (by
                        let _source_signature := (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input))
                        have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.R (M := M)) _value_i1 (Litex.isSet (Litex.R (M := M))) h_18) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_18))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i1 (Litex.isSet (Litex.R (M := M))) h_18))) h_26)
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
                        exact h_82 _arg_0 _member_0)))
                )
            )
          let _object_h403 := (Litex.fnSet (Litex.finiteSeqSignature _object_w15))
          have h_403 : Litex.In _value_i2 _object_h403 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 _object_w15 _object_h403 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet _object_w15) h_1)
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_sequence_x5f_carrier_x5f_widening_x2f_statement_x2e_lit
