import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonempty_x5f_family_x5f_choice_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]
variable [_indexedUnionSemantics : Litex.IndexedUnionSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.IsSet _value_i1) (h_2 : ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9 : Litex.In _value_i2 _value_i1), Litex.IsNonempty _value_i2), ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_10 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
    have h_10 : Litex.In _value_i4 _value_i1 := h_10
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.familyUnion _value_i1); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))), Litex.IsChoiceFunctionFor _value_i1 _value_i1 (Litex.formulaFnOn (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => _raw_i5) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote _value_i1) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => _raw_i5) _raw_i5) (Litex.denote _value_i1) := (by
    intro _raw_i5 h_59 _
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_59)
    have h_59 : Litex.In _value_i5 _value_i1 := h_59
    change Litex.In _value_i5 _value_i1
    exact h_59)
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _value_i1) (Litex.denote _value_i1) (Litex.isSet _value_i1) (Litex.isSet _value_i1) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard)) _value_i3 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8 h_2
          have h_78 : Litex.IsSet _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_92 : ∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (h_94 : Litex.In _value_i14 (let _checked_header : ∀ (_raw_i13 : M.Value), M.mem _raw_i13 (Litex.denote _value_i1) → ((fun (_raw_i13 : M.Value) => True) _raw_i13) → True := (by
              intro _raw_i13 h_93 _
              let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_93)
              have h_93 : Litex.In _value_i13 _value_i1 := h_93
              exact True.intro);
            Litex.fnSet (let _litex_output := (Litex.familyUnion _value_i1); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input)))), Litex.IsChoiceFunctionFor _value_i1 _value_i1 (Litex.formulaFnOn (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => _raw_i15) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i15 : M.Value), M.mem _raw_i15 (Litex.denote _value_i1) → ((fun (_raw_i15 : M.Value) => True) _raw_i15) → M.mem ((fun (_raw_i15 : M.Value) => _raw_i15) _raw_i15) (Litex.denote _value_i1) := (by
              intro _raw_i15 h_142 _
              let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_142)
              have h_142 : Litex.In _value_i15 _value_i1 := h_142
              change Litex.In _value_i15 _value_i1
              exact h_142)
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _value_i1) (Litex.denote _value_i1) (Litex.isSet _value_i1) (Litex.isSet _value_i1) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard)) _value_i14 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_7 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_84 : Litex.In _value_i6 _value_i1), Litex.IsNonempty _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i6 _rep_i6 _value_i6 h_84
                              exact (h_2 _value_i6 h_84)
                            )
                          )
                      )
                    have h_80 : Litex.IsSet _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_78
                          )
                      )
                    have h_82 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_89 : Litex.In _value_i12 _value_i1), Litex.IsNonempty _value_i12 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i12 _rep_i12 _value_i12 h_89
                              exact (h_7 _value_i12 h_89)
                            )
                          )
                      )
                    exact Litex.choiceForIdentity _value_i1 (Litex.formulaFnOn (let _litex_output := _value_i1; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => _raw_i15) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i15 : M.Value), M.mem _raw_i15 (Litex.denote _value_i1) → ((fun (_raw_i15 : M.Value) => True) _raw_i15) → M.mem ((fun (_raw_i15 : M.Value) => _raw_i15) _raw_i15) (Litex.denote _value_i1) := (by
                        intro _raw_i15 h_142 _
                        let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_142)
                        have h_142 : Litex.In _value_i15 _value_i1 := h_142
                        change Litex.In _value_i15 _value_i1
                        exact h_142)
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _value_i1) (Litex.denote _value_i1) (Litex.isSet _value_i1) (Litex.isSet _value_i1) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard)) (by
                      intro x hx
                      exact Litex.formulaIdentityCall _ (fun _ => rfl) x ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)) (fun a ha => h_82 (Litex.objectAtLevel (Litex.denote a) (Litex.isSet a)) ha)
                  )
                )
            )
          exact h_92
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonempty_x5f_family_x5f_choice_x2f_statement_x2e_lit
