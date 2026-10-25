import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_infinite_x5f_sequence_x5f_values_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_21 : Litex.In _value_i2 (Litex.seqSet _value_i1 h_17)) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_23 : Litex.In _value_i3 (Litex.NPos (M := M))), (by
  let _object_h22 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet _value_i1 h_17).val.carrier))
  have h_22 : Litex.In _value_i2 _object_h22 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i2 _value_i2 (Litex.seqSet _value_i1 h_17) _object_h22 (Litex.sameRefl _value_i2) (Litex.seqSet_eq_fnSet (Litex.seqSet _value_i1 h_17)) h_21)
        )
    )
  let _object_w5 := (let _litex_call_arg_0 := _value_i3;
  Litex.callOnDomain (Litex.NPos (M := M)) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_22 h_23 True.intro)
  exact (by
    let _atomic_wd_1_0 := _object_w5
    exact Litex.In _atomic_wd_1_0 _value_i1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_21 _Host_i3 _rep_i3 _value_i3 h_23
          let _object_h22 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet _value_i1 h_17).val.carrier))
          have h_22 : Litex.In _value_i2 _object_h22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.seqSet _value_i1 h_17) _object_h22 (Litex.sameRefl _value_i2) (Litex.seqSet_eq_fnSet (Litex.seqSet _value_i1 h_17)) h_21)
                )
            )
          have h_24 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i3 h_23)
                )
            )
          have h_25 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_24)
                )
            )
          have h_26 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_24) _litex_zero.symm)
                )
            )
          let _object_w5 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOnDomain (Litex.NPos (M := M)) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_22 h_23 True.intro)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w5
            exact Litex.In _atomic_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call _value_i1 _value_i1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _value_i1) (Litex.callOnInOutput _litex_return_call)))
                )
            )
          exact h_1
        )
      )
  )

theorem h_51 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_83 : Litex.In _value_i5 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_85 : Litex.In _value_i6 (Litex.NPos (M := M))), (by
  let _object_h84 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
  have h_84 : Litex.In _value_i5 _object_h84 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i5 _value_i5 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h84 (Litex.sameRefl _value_i5) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_83)
        )
    )
  let _object_w10 := (let _litex_call_arg_0 := _value_i6;
  Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i5 _litex_call_arg_0 h_84 h_85 True.intro)
  exact (by
    let _atomic_wd_1_0 := _object_w10
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_83 _Host_i6 _rep_i6 _value_i6 h_85
          let _object_h84 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_84 : Litex.In _value_i5 _object_h84 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i5 _value_i5 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h84 (Litex.sameRefl _value_i5) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_83)
                )
            )
          have h_86 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i6 h_85)
                )
            )
          have h_87 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i6 h_86)
                )
            )
          have h_88 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i6 h_86) _litex_zero.symm)
                )
            )
          let _object_w10 := (let _litex_call_arg_0 := _value_i6;
          Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i5 _litex_call_arg_0 h_84 h_85 True.intro)
          have h_50 : (by
            let _atomic_wd_1_0 := _object_w10
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w10
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))
                )
            )
          exact h_50
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_infinite_x5f_sequence_x5f_values_x2f_statement_x2e_lit
