import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_function_x5f_preimages_x2f_statement_x2e_lit

universe u v1 v3 v4 v8 v10
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_37 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
    intro _raw_i2 h_36 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_36)
    have h_36 : Litex.In _value_i2 (Litex.R (M := M)) := h_36
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i2 = (M.number (0 : ℂ))))
              exact h_1)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_38 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_39 : Litex.In _value_i4 (Litex.R (M := M))) (h_2 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))) (h_3 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _value_i1 _value_i3 h_37 h_38 h_2)
  exact Litex.Same _equal_wd_1_0 _value_i4)), (by
  let _object_w21 := (by
    let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i5 : Litex.Obj (M := M) M.Value) (h_54 : Litex.In _value_i5 (Litex.R (M := M))) => ∃ (h_52 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _value_i1 _value_i5 h_37 h_54 h_52) _value_i4))
    exact Litex.preimage _value_i1 _value_i4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
      intro _raw_i2 h_36 h_1
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_36)
      have h_36 : Litex.In _value_i2 (Litex.R (M := M)) := h_36
      have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i2 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_37))
  exact (by
    let _atomic_wd_1_1 := _object_w21
    exact Litex.In _value_i3 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_37 _Host_i3 _rep_i3 _value_i3 h_38 _Host_i4 _rep_i4 _value_i4 h_39 h_2 h_3
          let _object_w21 := (by
            let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i5 : Litex.Obj (M := M) M.Value) (h_54 : Litex.In _value_i5 (Litex.R (M := M))) => ∃ (h_52 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _value_i1 _value_i5 h_37 h_54 h_52) _value_i4))
            exact Litex.preimage _value_i1 _value_i4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
              intro _raw_i2 h_36 h_1
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_36)
              have h_36 : Litex.In _value_i2 (Litex.R (M := M)) := h_36
              have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i2 = (M.number (0 : ℂ))))
                        exact h_1)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_37))
          have h_4 : (by
            let _atomic_wd_1_1 := _object_w21
            exact Litex.In _value_i3 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w21
                    exact (by
                      let _preimage := _atomic_wd_1_1
                      let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_84 : Litex.In _value_i6 (Litex.R (M := M))) => ∃ (h_82 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _value_i1 _value_i6 h_37 h_84 h_82) _value_i4))
                      have _preimage_same : (Litex.denote _value_i3) = (Litex.denote _value_i3) := rfl
                      exact (Litex.preimageMembers _preimage (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                        intro _raw_i2 h_36 h_1
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_36)
                        have h_36 : Litex.In _value_i2 (Litex.R (M := M)) := h_36
                        have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  change (¬ (_raw_i2 = (M.number (0 : ℂ))))
                                  exact h_1)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_37) (Litex.denote _value_i3)).mpr ⟨Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))).domain) _preimage_same) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (Litex.denote _value_i3)).mpr ⟨h_38, h_2⟩), Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote _preimage.val.function) x = Litex.denote _preimage.val.target) _preimage_same) h_3⟩))
                )
            )
          exact h_4
        )
      )
  )

theorem h_117 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_149 : Litex.In _value_i8 (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _raw_i9) → True := (by
    intro _raw_i9 h_148 h_115
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_148)
    have h_148 : Litex.In _value_i9 (Litex.R (M := M)) := h_148
    have h_115 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i9 = (M.number (0 : ℂ))))
              exact h_115)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ)))))))) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_150 : Litex.In _value_i10 (Litex.R (M := M))), (by
  let _object_w42 := (by
    let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_153 : Litex.In _value_i11 (Litex.R (M := M))) => ∃ (h_151 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _value_i8 _value_i11 h_149 h_153 h_151) _value_i10))
    exact Litex.preimage _value_i8 _value_i10 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ)))))) (Litex.inOfSame _value_i8 _value_i8 (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _raw_i9) → True := (by
      intro _raw_i9 h_148 h_115
      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_148)
      have h_148 : Litex.In _value_i9 (Litex.R (M := M)) := h_148
      have h_115 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i9 = (M.number (0 : ℂ))))
                exact h_115)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_149))
  exact (by
    let _atomic_wd_1_0 := _object_w42
    exact Litex.Subset _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 h_149 _Host_i10 _rep_i10 _value_i10 h_150
          let _object_w42 := (by
            let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_153 : Litex.In _value_i11 (Litex.R (M := M))) => ∃ (h_151 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _value_i8 _value_i11 h_149 h_153 h_151) _value_i10))
            exact Litex.preimage _value_i8 _value_i10 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ)))))) (Litex.inOfSame _value_i8 _value_i8 (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _raw_i9) → True := (by
              intro _raw_i9 h_148 h_115
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_148)
              have h_148 : Litex.In _value_i9 (Litex.R (M := M)) := h_148
              have h_115 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i9 = (M.number (0 : ℂ))))
                        exact h_115)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_149))
          have h_116 : (by
            let _atomic_wd_1_0 := _object_w42
            exact Litex.Subset _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w42
                    exact (by
                      let _preimage := _atomic_wd_1_0
                      let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_166 : Litex.In _value_i12 (Litex.R (M := M))) => ∃ (h_164 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _value_i8 _value_i12 h_149 h_166 h_164) _value_i10))
                      change Litex.Subset _preimage (Litex.R (M := M))
                      intro _preimage_input _preimage_member
                      have _preimage_domain := ((Litex.preimageMembers _preimage (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ)))))) (Litex.inOfSame _value_i8 _value_i8 (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _raw_i9) → True := (by
                        intro _raw_i9 h_148 h_115
                        let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_148)
                        have h_148 : Litex.In _value_i9 (Litex.R (M := M)) := h_148
                        have h_115 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  change (¬ (_raw_i9 = (M.number (0 : ℂ))))
                                  exact h_115)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_149) _preimage_input).mp _preimage_member).1
                      obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _litex_input) _).mp _preimage_domain
                      have _preimage_guard_0 := _preimage_guard
                      have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
                      exact Eq.mp (congrArg (M.mem _preimage_input) (Litex.sameRefl (Litex.R (M := M)))) _preimage_base))
                )
            )
          exact h_116
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_function_x5f_preimages_x2f_statement_x2e_lit
