import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_infinite_x5f_sequence_x5f_spaces_x2f_statement_x2e_lit

universe u v1 v4 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1)

noncomputable def _object_w1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) := (Litex.seqSet _value_i1 h_1)

theorem h_2 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : (by
  let _atomic_wd_1_0 := (_object_w1 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)
  exact Litex.IsSet _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w1 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)
          exact (Litex.isSet _atomic_wd_1_0))
      )
  )

noncomputable def _object_i2 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) := (_object_w1 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)
theorem h_10 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : Litex.Same (_object_i2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) (_object_w1 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_w1 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1))
      )
  )

theorem h_11 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : (by
  let _equal_wd_1_1 := (_object_w1 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)
  exact Litex.Same (_object_i2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_10 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)
      )
  )

noncomputable def _object_w2 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) := (Litex.seqSet (_object_i2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) (Litex.isSetOfSame (_object_w1 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) (_object_i2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) ((h_10 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)).symm (h_2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)))

theorem h_13 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : (by
  let _atomic_wd_1_0 := (_object_w2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)
  exact Litex.IsSet _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)
          exact (Litex.isSet _atomic_wd_1_0))
      )
  )

noncomputable def _object_w5 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) := (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))

noncomputable def _object_w6 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_41 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_41)
    have h_41 : Litex.In _value_i3 (Litex.NPos (M := M)) := h_41
    have h_42 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inNPos_positive _value_i3 h_41)
          )
      )
    have h_43 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_42)
          )
      )
    have h_44 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_42) _litex_zero.symm)
          )
      )
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)))

theorem h_27 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : (by
  let _equal_wd_1_0 := (_object_w5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)
  let _equal_wd_1_1 := (_object_w6 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1);
        let _equal_wd_1_1 := (_object_w6 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1);
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.seqSet_eq_fnSet _equal_wd_1_0)))
      )
  )

theorem h_50 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_51 : Litex.IsSet _value_i4), (by
  let _object_w9 := (Litex.seqSet _value_i4 h_51)
  let _object_w10 := (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → True := (by
      intro _raw_i5 h_55 _
      let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_55)
      have h_55 : Litex.In _value_i5 (Litex.NPos (M := M)) := h_55
      have h_56 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inNPos_positive _value_i5 h_55)
            )
        )
      have h_57 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i5 h_56)
            )
        )
      have h_58 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i5 h_56) _litex_zero.symm)
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := _value_i4; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)))
  exact (by
    let _equal_wd_1_0 := _object_w9
    let _equal_wd_1_1 := _object_w10
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_51
          let _object_w9 := (Litex.seqSet _value_i4 h_51)
          let _object_w10 := (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → True := (by
              intro _raw_i5 h_55 _
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_55)
              have h_55 : Litex.In _value_i5 (Litex.NPos (M := M)) := h_55
              have h_56 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inNPos_positive _value_i5 h_55)
                    )
                )
              have h_57 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i5 h_56)
                    )
                )
              have h_58 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i5 h_56) _litex_zero.symm)
                    )
                )
              exact True.intro);
            Litex.fnSet (let _litex_output := _value_i4; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)))
          have h_49 : (by
            let _equal_wd_1_0 := _object_w9
            let _equal_wd_1_1 := _object_w10
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w9;
                  let _equal_wd_1_1 := _object_w10;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.seqSet_eq_fnSet _equal_wd_1_0)))
                )
            )
          exact h_49
        )
      )
  )

theorem h_64 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_66 : Litex.IsSet _value_i6), (by
  let _object_w13 := (let _checked_header : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → True := (by
      intro _raw_i7 h_67 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_67)
      have h_67 : Litex.In _value_i7 (Litex.NPos (M := M)) := h_67
      have h_68 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inNPos_positive _value_i7 h_67)
            )
        )
      have h_69 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_68)
            )
        )
      have h_70 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_68) _litex_zero.symm)
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := _value_i6; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)))
  let _object_w14 := (Litex.seqSet _value_i6 h_66)
  exact (by
    let _equal_wd_1_0 := _object_w13
    let _equal_wd_1_1 := _object_w14
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_66
          let _object_w13 := (let _checked_header : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → True := (by
              intro _raw_i7 h_67 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_67)
              have h_67 : Litex.In _value_i7 (Litex.NPos (M := M)) := h_67
              have h_68 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inNPos_positive _value_i7 h_67)
                    )
                )
              have h_69 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_68)
                    )
                )
              have h_70 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_68) _litex_zero.symm)
                    )
                )
              exact True.intro);
            Litex.fnSet (let _litex_output := _value_i6; Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)))
          let _object_w14 := (Litex.seqSet _value_i6 h_66)
          have h_63 : (by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w13;
                  let _equal_wd_1_1 := _object_w14;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.seqSet_eq_fnSet _equal_wd_1_1).symm))
                )
            )
          exact h_63
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_infinite_x5f_sequence_x5f_spaces_x2f_statement_x2e_lit
