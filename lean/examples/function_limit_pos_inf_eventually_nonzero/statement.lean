import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_pos_x5f_inf_x5f_eventually_x5f_nonzero_x2f_statement_x2e_lit

universe u v1 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_7 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
    have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_9 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_7 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_7 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_7 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_8)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_12 : Litex.In _value_i3 (Litex.R (M := M)) := h_9
  exact Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i3)) (h_2 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_19 : Litex.In _value_i4 (Litex.R (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i5 : Litex.Obj (M := M) M.Value) (h_20 : Litex.In _value_i5 (Litex.R (M := M))) => Litex.Lt _value_i4 _value_i5)) (by
  have _preimage_target : Litex.IsSet (Litex.RStar (M := M)) := (Litex.isSet (Litex.RStar (M := M)))
  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i7 : Litex.Obj (M := M) M.Value) (h_52 : Litex.In _value_i7 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _value_i7 h_8 h_52 True.intro) (Litex.RStar (M := M))))
  exact Litex.preimageSet _value_i1 (Litex.RStar (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_7 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
    have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_7 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
    have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_8)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8 _Host_i3 _rep_i3 _value_i3 h_9 h_1 h_2
          have h_65 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_64 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_64)
              have h_64 : Litex.In _value_i2 (Litex.R (M := M)) := h_64
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_66 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_85 : ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_158 : Litex.In _value_i8 (Litex.R (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_159 : Litex.In _value_i9 (Litex.R (M := M))) => Litex.Lt _value_i8 _value_i9)) (by
            have _preimage_target : Litex.IsSet (Litex.RStar (M := M)) := (Litex.isSet (Litex.RStar (M := M)))
            let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_191 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _value_i13 h_65 h_191 True.intro) (Litex.RStar (M := M))))
            exact Litex.preimageSet _value_i1 (Litex.RStar (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_64 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_64)
              have h_64 : Litex.In _value_i2 (Litex.R (M := M)) := h_64
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_64 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_64)
              have h_64 : Litex.In _value_i2 (Litex.R (M := M)) := h_64
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_65)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_78 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_64 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_64)
                          have h_64 : Litex.In _value_i2 (Litex.R (M := M)) := h_64
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_64 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_64)
                                  have h_64 : Litex.In _value_i2 (Litex.R (M := M)) := h_64
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                              exact h_65)
                          )
                      )
                    have h_79 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_80 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_79
                          )
                      )
                    have h_81 : Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i3 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_82 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    exact (show ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_108 : Litex.In _value_i8 (Litex.R (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_109 : Litex.In _value_i9 (Litex.R (M := M))) => Litex.Lt _value_i8 _value_i9)) (by
                    have _preimage_target : Litex.IsSet (Litex.RStar (M := M)) := (Litex.isSet (Litex.RStar (M := M)))
                    let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_143 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _value_i12 h_78 h_143 True.intro) (Litex.RStar (M := M))))
                    exact Litex.preimageSet _value_i1 (Litex.RStar (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_64 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_64)
                      have h_64 : Litex.In _value_i2 (Litex.R (M := M)) := h_64
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_64 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_64)
                      have h_64 : Litex.In _value_i2 (Litex.R (M := M)) := h_64
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_78)) from (by
                    let _law0_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_64 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_64)
                      have h_64 : Litex.In _value_i2 (Litex.R (M := M)) := h_64
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                    have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_78
                    let _law0_source_domain := (M.standard Litex.StandardSetValue.real)
                    have _law0_domain_set : M.isSet _law0_source_domain := (Litex.isSet (Litex.R (M := M)))
                    have _law0_domain_match : _law0_source_domain = _law0_signature.domain := by
                      apply Litex.SetSemantics.ext _ _ _law0_domain_set _law0_signature.domain_isSet
                      intro x
                      change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
                      rw [Litex.SetSemantics.sep_members]
                      exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                    let _law0_domain := Litex.semanticObject _law0_source_domain _law0_domain_set
                    have _law_real_0 : Litex.RealFunctionValue M (Litex.denote _value_i1) := by
                      refine ⟨_law0_signature, _law0_member, ?_, h_80⟩
                      intro x hx
                      exact h_79 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                    obtain ⟨_threshold, _threshold_member, _control⟩ := Litex.infiniteFunctionLimitEventuallyNonzero .positive _value_i1 _value_i3 _law0_domain _law_real_0 _law_domain_0 h_81 h_82
                    refine ⟨_threshold, _threshold_member, ?_⟩
                    exact _control
                  ))
                  )
                )
            )
          exact h_85
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_pos_x5f_inf_x5f_eventually_x5f_nonzero_x2f_statement_x2e_lit
