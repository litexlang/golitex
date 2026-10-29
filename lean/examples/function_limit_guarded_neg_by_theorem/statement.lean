import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_guarded_x5f_neg_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2 v4 v5 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_7 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_10 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
    intro _raw_i3 h_9 h_1
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_9)
    have h_9 : Litex.In _value_i3 (Litex.R (M := M)) := h_9
    have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i3 = (M.number (0 : ℂ))))
              exact h_1)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_11 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
    intro _raw_i3 h_9 h_1
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_9)
    have h_9 : Litex.In _value_i3 (Litex.R (M := M)) := h_9
    have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i3 = (M.number (0 : ℂ))))
              exact h_1)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_12 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_13 : Litex.In _value_i5 (Litex.R (M := M))) (h_2 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
      intro _raw_i3 h_9 h_1
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_9)
      have h_9 : Litex.In _value_i3 (Litex.R (M := M)) := h_9
      have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
      intro _raw_i3 h_9 h_1
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_9)
      have h_9 : Litex.In _value_i3 (Litex.R (M := M)) := h_9
      have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
      intro _raw_i3 h_9 h_1
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_9)
      have h_9 : Litex.In _value_i3 (Litex.R (M := M)) := h_9
      have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_10)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_16 : Litex.In _value_i4 (Litex.R (M := M)) := h_12
  have h_25 : Litex.In _value_i5 (Litex.R (M := M)) := h_13
  exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i4 _value_i5)) (h_5 : ∀ (_value_i6 : Litex.Obj (M := M) M.Value) (h_37 : Litex.In _value_i6 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i7 : Litex.Obj (M := M) M.Value) (h_36 : Litex.In _value_i7 (Litex.R (M := M))) => ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ))))), (by
  have h_38 : (M.mem (Litex.denote _value_i6) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i7 : Litex.Obj (M := M) M.Value) (h_36 : Litex.In _value_i7 (Litex.R (M := M))) => ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i6 _litex_builder).mp h_37)).choose
        )
    )
  have h_39 : (¬ ((Litex.denote _value_i6) = (M.number (0 : ℂ)))) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i7 : Litex.Obj (M := M) M.Value) (h_36 : Litex.In _value_i7 (Litex.R (M := M))) => ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i6 _litex_builder).mp h_37)).choose_spec
        )
    )
  exact (by
    let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _value_i2 _value_i6 h_11 h_38 h_39)
    let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _value_i1 _value_i6 h_10 h_38 h_39);
    (Litex.neg _wd_1_0 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
)), (by
  let _atomic_wd_1_2 := (Litex.neg _value_i5 (M.real_subset_complex _ h_13))
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
      intro _raw_i3 h_9 h_1
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_9)
      have h_9 : Litex.In _value_i3 (Litex.R (M := M)) := h_9
      have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))).val
    have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
      intro _raw_i3 h_9 h_1
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_9)
      have h_9 : Litex.In _value_i3 (Litex.R (M := M)) := h_9
      have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
      intro _raw_i3 h_9 h_1
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_9)
      have h_9 : Litex.In _value_i3 (Litex.R (M := M)) := h_9
      have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_11)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_243 : Litex.In _value_i4 (Litex.R (M := M)) := h_12
  have h_252 : (by
    let _atomic_wd_2_0 := _atomic_wd_1_2
    exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
    let _atomic_wd_2_0 := _atomic_wd_1_2
    exact (Litex.negInR _value_i5 h_13))
  exact Litex.HasFiniteFunctionLimit .both _value_i2 _value_i4 _atomic_wd_1_2) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_10 _Host_i2 _rep_i2 _value_i2 h_11 _Host_i4 _rep_i4 _value_i4 h_12 _Host_i5 _rep_i5 _value_i5 h_13 h_2 h_5
          have h_299 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
              intro _raw_i3 h_298 h_1
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_298)
              have h_298 : Litex.In _value_i3 (Litex.R (M := M)) := h_298
              have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                        exact h_1)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_300 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
              intro _raw_i3 h_298 h_1
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_298)
              have h_298 : Litex.In _value_i3 (Litex.R (M := M)) := h_298
              have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                        exact h_1)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_301 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_302 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          have h_8 : (by
            let _atomic_wd_1_2 := (Litex.neg _value_i5 (M.real_subset_complex _ h_302))
            exact Litex.HasFiniteFunctionLimit .both _value_i2 _value_i4 _atomic_wd_1_2) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_509 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
                          intro _raw_i3 h_298 h_1
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_298)
                          have h_298 : Litex.In _value_i3 (Litex.R (M := M)) := h_298
                          have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                                    exact h_1)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
                                  intro _raw_i3 h_298 h_1
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_298)
                                  have h_298 : Litex.In _value_i3 (Litex.R (M := M)) := h_298
                                  have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (by
                                            change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                                            exact h_1)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))
                              exact h_299)
                          )
                      )
                    have h_510 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_511 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_510
                          )
                      )
                    have h_512 : Litex.In _value_i4 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_301
                          )
                      )
                    have h_515 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
                          intro _raw_i3 h_298 h_1
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_298)
                          have h_298 : Litex.In _value_i3 (Litex.R (M := M)) := h_298
                          have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                                    exact h_1)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
                                  intro _raw_i3 h_298 h_1
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_298)
                                  have h_298 : Litex.In _value_i3 (Litex.R (M := M)) := h_298
                                  have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (by
                                            change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                                            exact h_1)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))
                              exact h_300)
                          )
                      )
                    have h_516 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_510
                          )
                      )
                    have h_517 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_510
                          )
                      )
                    have h_518 : (by
                      let _equal_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_571 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))
                      let _equal_wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_572 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))
                      exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_519 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i4 _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    have h_521 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_582 : Litex.In _value_i9 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_572 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))), (by
                      have h_583 : (M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_572 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i9 _litex_builder).mp h_582)).choose
                            )
                        )
                      have h_584 : (¬ ((Litex.denote _value_i9) = (M.number (0 : ℂ)))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_572 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i9 _litex_builder).mp h_582)).choose_spec
                            )
                        )
                      exact Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _value_i2 _value_i9 h_515 h_583 h_584) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _value_i1 _value_i9 h_509 h_583 h_584);
                      (Litex.neg _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i9 _rep_i9 _value_i9 h_582
                              have h_583 : (M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_572 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i9 _litex_builder).mp h_582)).choose
                                    )
                                )
                              have h_584 : (¬ ((Litex.denote _value_i9) = (M.number (0 : ℂ)))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_572 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i9 _litex_builder).mp h_582)).choose_spec
                                    )
                                )
                              exact (h_5 (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) h_582)
                            )
                          )
                      )
                    have h_522 : Litex.HasFiniteFunctionLimit .both _value_i2 _value_i4 (Litex.neg _value_i5 (M.real_subset_complex _ h_302)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              let _atomic_wd_1_2 := (Litex.neg _value_i5 (M.real_subset_complex _ h_302))
                              have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
                                let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
                                  intro _raw_i3 h_298 h_1
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_298)
                                  have h_298 : Litex.In _value_i3 (Litex.R (M := M)) := h_298
                                  have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (by
                                            change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                                            exact h_1)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))).val
                                have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
                                  intro _raw_i3 h_298 h_1
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_298)
                                  have h_298 : Litex.In _value_i3 (Litex.R (M := M)) := h_298
                                  have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (by
                                            change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                                            exact h_1)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
                                  intro _raw_i3 h_298 h_1
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_298)
                                  have h_298 : Litex.In _value_i3 (Litex.R (M := M)) := h_298
                                  have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (by
                                            change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                                            exact h_1)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_515)
                                have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_510
                                have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_510
                                refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                                intro x hx
                                exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              )
                              have h_877 : Litex.In _value_i4 (Litex.R (M := M)) := h_512
                              have h_884 : (by
                                let _atomic_wd_2_0 := _atomic_wd_1_2
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
                                let _atomic_wd_2_0 := _atomic_wd_1_2
                                exact (Litex.negInR _value_i5 h_302))
                              exact Litex.HasFiniteFunctionLimit .both _value_i2 _value_i4 _atomic_wd_1_2) from (by
                              let _law0_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
                                intro _raw_i3 h_298 h_1
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_298)
                                have h_298 : Litex.In _value_i3 (Litex.R (M := M)) := h_298
                                have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (by
                                          change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                                          exact h_1)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))).val
                              have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_509
                              let _law0_source_domain := (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i3 : M.Value) => ∃ (_ : M.mem _raw_i3 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i3 = (M.number (0 : ℂ))))))
                              have _law0_domain_set : M.isSet _law0_source_domain := (Litex.SetSemantics.sep_isSet (Litex.denote (Litex.R (M := M))) _ (Litex.isSet (Litex.R (M := M))))
                              have _law0_domain_match : _law0_source_domain = _law0_signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _law0_domain_set _law0_signature.domain_isSet
                                intro x
                                change M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _)
                                rw [Litex.SetSemantics.sep_members, Litex.SetSemantics.sep_members]
                                exact ⟨fun ⟨hx, _, hg⟩ => ⟨hx, hg⟩, fun ⟨hx, hg⟩ => ⟨hx, hx, hg⟩⟩
                              let _law0_domain := Litex.semanticObject _law0_source_domain _law0_domain_set
                              have _law_real_0 : Litex.RealFunctionValue M (Litex.denote _value_i1) := by
                                refine ⟨_law0_signature, _law0_member, ?_, h_511⟩
                                intro x hx
                                exact h_510 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                              let _law1_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
                                intro _raw_i3 h_298 h_1
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_298)
                                have h_298 : Litex.In _value_i3 (Litex.R (M := M)) := h_298
                                have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (by
                                          change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                                          exact h_1)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))).val
                              have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_515
                              let _law1_source_domain := (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i3 : M.Value) => ∃ (_ : M.mem _raw_i3 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i3 = (M.number (0 : ℂ))))))
                              have _law1_domain_set : M.isSet _law1_source_domain := (Litex.SetSemantics.sep_isSet (Litex.denote (Litex.R (M := M))) _ (Litex.isSet (Litex.R (M := M))))
                              have _law1_domain_match : _law1_source_domain = _law1_signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _law1_domain_set _law1_signature.domain_isSet
                                intro x
                                change M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _)
                                rw [Litex.SetSemantics.sep_members, Litex.SetSemantics.sep_members]
                                exact ⟨fun ⟨hx, _, hg⟩ => ⟨hx, hg⟩, fun ⟨hx, hg⟩ => ⟨hx, hx, hg⟩⟩
                              let _law1_domain := Litex.semanticObject _law1_source_domain _law1_domain_set
                              have _law_real_1 : Litex.RealFunctionValue M (Litex.denote _value_i2) := by
                                refine ⟨_law1_signature, _law1_member, ?_, h_517⟩
                                intro x hx
                                exact h_516 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                              exact Litex.finiteFunctionLimitMap .both (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i4) (Litex.denote _value_i5) (Litex.denote (Litex.neg _value_i5 (M.real_subset_complex _ h_302))) _law_real_0 _law_real_1 (_law_domain_1.symm.trans (h_518.trans _law_domain_0)) M.negValue (fun x : ℝ => -x) (by intro x; rw [M.neg_numbers, Complex.ofReal_neg]) rfl (by
                                intro input hinput
                                have _law_input : M.mem input (Litex.denote _law0_domain) := by
                                  rw [_law_domain_0]
                                  exact hinput
                                exact h_521 (Litex.semanticObject input (M.member_isSet _law_input)) _law_input
                              ) continuous_neg h_519
                            ))
                          )
                      )
                    exact (by
                    let _atomic_wd_1_2 := (Litex.neg _value_i5 (M.real_subset_complex _ h_302))
                    exact h_522)
                  )
                )
            )
          exact (by
            let _atomic_wd_1_2 := (Litex.neg _value_i5 (M.real_subset_complex _ h_302))
            exact h_8)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_guarded_x5f_neg_x5f_by_x5f_theorem_x2f_statement_x2e_lit
