import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_function_x5f_limit_x5f_guarded_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v3 v4 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_12 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
    intro _raw_i2 h_14 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
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
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_16 : Litex.In _value_i3 (Litex.R (M := M))) (h_7 : ∀ (_value_i4 : Litex.Obj (M := M) M.Value) (h_17 : Litex.In _value_i4 (Litex.RPos (M := M))), ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_23 : Litex.In _value_i5 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_21 : Litex.In _value_i6 (Litex.R (M := M))) => ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))))), (by
  have h_24 : (M.mem (Litex.denote _value_i5) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_21 : Litex.In _value_i6 (Litex.R (M := M))) => ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i5 _litex_builder).mp h_23)).choose
        )
    )
  exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i5 _value_i3 (M.real_subset_complex _ h_24) (M.real_subset_complex _ h_16));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i5 _value_i3 h_24 h_16))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i5 _value_i3 (M.real_subset_complex _ h_24) (M.real_subset_complex _ h_16));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i5 _value_i3 h_24 h_16)))) _value_i4))
)) (h_10 : ∀ (_value_i7 : Litex.Obj (M := M) M.Value) (h_1153 : Litex.In _value_i7 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_1152 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ))))), (by
  have h_1154 : (M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_1152 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i7 _litex_builder).mp h_1153)).choose
        )
    )
  have h_1155 : (¬ ((Litex.denote _value_i7) = (M.number (0 : ℂ)))) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_1152 : Litex.In _value_i8 (Litex.R (M := M))) => ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i7 _litex_builder).mp h_1153)).choose_spec
        )
    )
  exact (by
    let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _value_i1 _value_i7 h_15 h_1154 h_1155)
    exact Litex.Same _equal_wd_1_0 _value_i7)
)), Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i3 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15 _Host_i3 _rep_i3 _value_i3 h_16 h_7 h_10
          have h_1187 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
              intro _raw_i2 h_1186 h_1
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1186)
              have h_1186 : Litex.In _value_i2 (Litex.R (M := M)) := h_1186
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
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          have h_1188 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_16
                )
            )
          have h_13 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_2344 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                          intro _raw_i2 h_1186 h_1
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1186)
                          have h_1186 : Litex.In _value_i2 (Litex.R (M := M)) := h_1186
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
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                                  intro _raw_i2 h_1186 h_1
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1186)
                                  have h_1186 : Litex.In _value_i2 (Litex.R (M := M)) := h_1186
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
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))
                              exact h_1187)
                          )
                      )
                    have h_2345 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_2346 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2345
                          )
                      )
                    have h_2347 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1188
                          )
                      )
                    have h_2348 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2347
                          )
                      )
                    have h_2353 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_2390 : Litex.In _value_i9 (Litex.RPos (M := M))), ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_2396 : Litex.In _value_i10 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2394 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))))), (by
                      have h_2397 : (M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2394 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i10 _litex_builder).mp h_2396)).choose
                            )
                        )
                      exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i10 _value_i3 (M.real_subset_complex _ h_2397) (M.real_subset_complex _ h_2347));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR _value_i10 _value_i3 h_2397 h_2347))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i10 _value_i3 (M.real_subset_complex _ h_2397) (M.real_subset_complex _ h_2347));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR _value_i10 _value_i3 h_2397 h_2347)))) _value_i9))
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i9 _rep_i9 _value_i9 h_2390
                              have h_2391 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRPos_positive _value_i9 h_2390)
                                    )
                                )
                              have h_2392 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_2391)
                                    )
                                )
                              have h_2393 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_2391) _litex_zero.symm)
                                    )
                                )
                              exact (h_7 (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) h_2390)
                            )
                          )
                      )
                    have h_2355 : ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_4128 : Litex.In _value_i11 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_4127 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))))), (by
                      have h_4129 : (M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_4127 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i11 _litex_builder).mp h_4128)).choose
                            )
                        )
                      have h_4130 : (¬ ((Litex.denote _value_i11) = (M.number (0 : ℂ)))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_4127 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i11 _litex_builder).mp h_4128)).choose_spec
                            )
                        )
                      exact Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _value_i1 _value_i11 h_2344 h_4129 h_4130) _value_i11
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i11 _rep_i11 _value_i11 h_4128
                              have h_4129 : (M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_4127 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i11 _litex_builder).mp h_4128)).choose
                                    )
                                )
                              have h_4130 : (¬ ((Litex.denote _value_i11) = (M.number (0 : ℂ)))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_4127 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i11 _litex_builder).mp h_4128)).choose_spec
                                    )
                                )
                              exact (h_10 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) h_4128)
                            )
                          )
                      )
                    have h_2356 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i3 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                                let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                                  intro _raw_i2 h_1186 h_1
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1186)
                                  have h_1186 : Litex.In _value_i2 (Litex.R (M := M)) := h_1186
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
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val
                                have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                                  intro _raw_i2 h_1186 h_1
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1186)
                                  have h_1186 : Litex.In _value_i2 (Litex.R (M := M)) := h_1186
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
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                                  intro _raw_i2 h_1186 h_1
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1186)
                                  have h_1186 : Litex.In _value_i2 (Litex.R (M := M)) := h_1186
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
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_2344)
                                have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_2345
                                have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_2345
                                refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                                intro x hx
                                exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              )
                              have h_4155 : Litex.In _value_i3 (Litex.R (M := M)) := h_2347
                              have h_4162 : Litex.In _value_i3 (Litex.R (M := M)) := h_2347
                              exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i3) from (by
                              let _signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                                intro _raw_i2 h_1186 h_1
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1186)
                                have h_1186 : Litex.In _value_i2 (Litex.R (M := M)) := h_1186
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
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val
                              have _member : Litex.In _value_i1 (Litex.fnSet _signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                                intro _raw_i2 h_1186 h_1
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1186)
                                have h_1186 : Litex.In _value_i2 (Litex.R (M := M)) := h_1186
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
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                                intro _raw_i2 h_1186 h_1
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1186)
                                have h_1186 : Litex.In _value_i2 (Litex.R (M := M)) := h_1186
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
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_2344)
                              let _source_domain := (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i2 : M.Value) => ∃ (_ : M.mem _raw_i2 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i2 = (M.number (0 : ℂ))))))
                              have _domain_set : M.isSet _source_domain := (Litex.SetSemantics.sep_isSet (Litex.denote (Litex.R (M := M))) _ (Litex.isSet (Litex.R (M := M))))
                              have _domain_match : _source_domain = _signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
                                intro x
                                change M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _)
                                rw [Litex.SetSemantics.sep_members, Litex.SetSemantics.sep_members]
                                exact ⟨fun ⟨hx, _, hg⟩ => ⟨hx, hg⟩, fun ⟨hx, hg⟩ => ⟨hx, hx, hg⟩⟩
                              let _domain := Litex.semanticObject _source_domain _domain_set
                              have _constant_real_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                              let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                                intro _raw_i2 h_1186 h_1
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1186)
                                have h_1186 : Litex.In _value_i2 (Litex.R (M := M)) := h_1186
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
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val
                              have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                                intro _raw_i2 h_1186 h_1
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1186)
                                have h_1186 : Litex.In _value_i2 (Litex.R (M := M)) := h_1186
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
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                                intro _raw_i2 h_1186 h_1
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1186)
                                have h_1186 : Litex.In _value_i2 (Litex.R (M := M)) := h_1186
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
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_2344)
                              have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_2345
                              have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_2345
                              refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                              intro x hx
                              exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                            )
                              exact Litex.finiteFunctionLimitIdentity .both _value_i1 _value_i3 _domain _constant_real_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_2347 h_2353 h_2355
                            ))
                          )
                      )
                    exact h_2356
                  )
                )
            )
          exact h_13
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_function_x5f_limit_x5f_guarded_x5f_by_x5f_theorem_x2f_statement_x2e_lit
