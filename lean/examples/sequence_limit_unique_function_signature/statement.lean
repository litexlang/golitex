import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_unique_x5f_function_x5f_signature_x2f_statement_x2e_lit

universe u v1 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_10 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_6 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
    have h_6 : Litex.In _value_i2 (Litex.NPos (M := M)) := h_6
    have h_7 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inNPos_positive _value_i2 h_6)
          )
      )
    have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_7)
          )
      )
    have h_9 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_7) _litex_zero.symm)
          )
      )
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_11 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_12 : Litex.In _value_i4 (Litex.R (M := M))) (h_1 : (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_6 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
      have h_6 : Litex.In _value_i2 (Litex.NPos (M := M)) := h_6
      have h_7 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inNPos_positive _value_i2 h_6)
            )
        )
      have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_7)
            )
        )
      have h_9 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_7) _litex_zero.symm)
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))).val) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_6 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
      have h_6 : Litex.In _value_i2 (Litex.NPos (M := M)) := h_6
      have h_7 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inNPos_positive _value_i2 h_6)
            )
        )
      have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_7)
            )
        )
      have h_9 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_7) _litex_zero.symm)
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_6 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
      have h_6 : Litex.In _value_i2 (Litex.NPos (M := M)) := h_6
      have h_7 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inNPos_positive _value_i2 h_6)
            )
        )
      have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_7)
            )
        )
      have h_9 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_7) _litex_zero.symm)
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_10)
  have _sequence_limit_real : Litex.In _value_i3 (Litex.R (M := M)) := h_11
  exact Litex.HasSequenceLimit _value_i1 _value_i3)) (h_2 : (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_6 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
      have h_6 : Litex.In _value_i2 (Litex.NPos (M := M)) := h_6
      have h_7 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inNPos_positive _value_i2 h_6)
            )
        )
      have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_7)
            )
        )
      have h_9 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_7) _litex_zero.symm)
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))).val) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_6 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
      have h_6 : Litex.In _value_i2 (Litex.NPos (M := M)) := h_6
      have h_7 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inNPos_positive _value_i2 h_6)
            )
        )
      have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_7)
            )
        )
      have h_9 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_7) _litex_zero.symm)
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_6 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
      have h_6 : Litex.In _value_i2 (Litex.NPos (M := M)) := h_6
      have h_7 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inNPos_positive _value_i2 h_6)
            )
        )
      have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_7)
            )
        )
      have h_9 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_7) _litex_zero.symm)
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_10)
  have _sequence_limit_real : Litex.In _value_i4 (Litex.R (M := M)) := h_12
  exact Litex.HasSequenceLimit _value_i1 _value_i4)), Litex.Same _value_i3 _value_i4 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_10 _Host_i3 _rep_i3 _value_i3 h_11 _Host_i4 _rep_i4 _value_i4 h_12 h_1 h_2
          have h_28 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_24 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_24)
              have h_24 : Litex.In _value_i2 (Litex.NPos (M := M)) := h_24
              have h_25 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inNPos_positive _value_i2 h_24)
                    )
                )
              have h_26 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_25)
                    )
                )
              have h_27 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_25) _litex_zero.symm)
                    )
                )
              exact True.intro);
            Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_29 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_30 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_5 : Litex.Same _value_i3 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.sequenceLimitCandidatesEqual _value_i1 _value_i3 _value_i4 (Litex.unguardedFunctionDomain _value_i1 (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) h_28) h_29 h_30 h_1 h_2)
                )
            )
          exact h_5
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_unique_x5f_function_x5f_signature_x2f_statement_x2e_lit
