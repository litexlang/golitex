import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_function_x5f_membership_x5f_domains_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) _raw_i2) → True := (by
    rintro _raw_i2 h_12 ⟨h_1, h_2⟩
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12)
    have h_12 : Litex.In _value_i2 (Litex.R (M := M)) := h_12
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i2 = (M.number (0 : ℂ))))
              exact h_1)
          )
      )
    have h_2 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i2 = (M.number (1 : ℂ))))
              exact h_2)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ)))))))))), (by
  let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) _raw_i3) → True := (by
      rintro _raw_i3 h_16 ⟨h_3, h_4⟩
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_16)
      have h_16 : Litex.In _value_i3 (Litex.R (M := M)) := h_16
      have h_3 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i3 = (M.number (1 : ℂ))))
                exact h_3)
            )
        )
      have h_4 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                exact h_4)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i3 = (M.number (0 : ℂ)))))))))
  exact Litex.In _value_i1 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15
          have h_24 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) _raw_i2) → True := (by
              rintro _raw_i2 h_21 ⟨h_1, h_2⟩
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_21)
              have h_21 : Litex.In _value_i2 (Litex.R (M := M)) := h_21
              have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i2 = (M.number (0 : ℂ))))
                        exact h_1)
                    )
                )
              have h_2 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i2 = (M.number (1 : ℂ))))
                        exact h_2)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          have h_11 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))) _raw_i5) → True := (by
                rintro _raw_i5 h_199 ⟨h_9, h_10⟩
                let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_199)
                have h_199 : Litex.In _value_i5 (Litex.R (M := M)) := h_199
                have h_9 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          change (¬ (_raw_i5 = (M.number (1 : ℂ))))
                          exact h_9)
                      )
                  )
                have h_10 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          change (¬ (_raw_i5 = (M.number (0 : ℂ))))
                          exact h_10)
                      )
                  )
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ)))))))))
            exact Litex.In _value_i1 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _membership_function := _value_i1
                    let _membership_target := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) _raw_i4) → True := (by
                        rintro _raw_i4 h_28 ⟨h_7, h_8⟩
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_28)
                        have h_28 : Litex.In _value_i4 (Litex.R (M := M)) := h_28
                        have h_7 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  change (¬ (_raw_i4 = (M.number (1 : ℂ))))
                                  exact h_7)
                              )
                          )
                        have h_8 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                  exact h_8)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ)))))))))
                    have h_36 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_49 : Litex.In _value_i7 (Litex.R (M := M))) (h_31 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ))) (h_32 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (1 : ℂ))), ((Litex.In _value_i7 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i7 (Litex.number (M := M) (1 : ℂ))) ∧ (¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)))))) := (by
                      intro _Host_i7 _rep_i7 _value_i7 h_49 h_31 h_32
                      have h_33 : Litex.In _value_i7 (Litex.R (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              h_49
                            )
                        )
                      have h_34 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (1 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              h_32
                            )
                        )
                      have h_35 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              h_31
                            )
                        )
                      exact (And.intro h_33 (And.intro h_34 h_35))
                    )
                    have h_73 : ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_86 : Litex.In _value_i8 (Litex.R (M := M))) (h_68 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (1 : ℂ))) (h_69 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ))), ((Litex.In _value_i8 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ))) ∧ (¬ Litex.Same _value_i8 (Litex.number (M := M) (1 : ℂ)))))) := (by
                      intro _Host_i8 _rep_i8 _value_i8 h_86 h_68 h_69
                      have h_70 : Litex.In _value_i8 (Litex.R (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              h_86
                            )
                        )
                      have h_71 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              h_69
                            )
                        )
                      have h_72 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (1 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              h_68
                            )
                        )
                      exact (And.intro h_70 (And.intro h_71 h_72))
                    )
                    have h_26 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_117 : Litex.In _value_i4 (Litex.R (M := M))) (h_7 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ))) (h_8 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))), (by
                      let _object_w24 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) _value_i1 _value_i4 h_24 h_117 (And.intro h_8 h_7))
                      exact (by
                        let _atomic_wd_1_0 := _object_w24
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i4 _rep_i4 _value_i4 h_117 h_7 h_8
                              let _object_w24 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) _value_i1 _value_i4 h_24 h_117 (And.intro h_8 h_7))
                              have h_27 : (by
                                let _atomic_wd_1_0 := _object_w24
                                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w24
                                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))
                                    )
                                )
                              exact h_27
                            )
                          )
                      )
                    have h_25 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) _raw_i4) → True := (by
                        rintro _raw_i4 h_194 ⟨h_7, h_8⟩
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_194)
                        have h_194 : Litex.In _value_i4 (Litex.R (M := M)) := h_194
                        have h_7 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  change (¬ (_raw_i4 = (M.number (1 : ℂ))))
                                  exact h_7)
                              )
                          )
                        have h_8 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                  exact h_8)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _source_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))
                              have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) _raw_i2) → True := (by
                                rintro _raw_i2 h_21 ⟨h_1, h_2⟩
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_21)
                                have h_21 : Litex.In _value_i2 (Litex.R (M := M)) := h_21
                                have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (by
                                          change (¬ (_raw_i2 = (M.number (0 : ℂ))))
                                          exact h_1)
                                      )
                                  )
                                have h_2 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (by
                                          change (¬ (_raw_i2 = (M.number (1 : ℂ))))
                                          exact h_2)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_24)
                              have _same_domain : _source_signature.domain = _membership_target.val.domain := (Litex.SetSemantics.ext ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain_isSet ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))).domain_isSet (fun x => ⟨fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))).domain from by
                              intro _preimage_input _preimage_domain
                              obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) _litex_input) _).mp _preimage_domain
                              rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
                              have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
                              have _domain_target := h_36 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0 _preimage_guard_1
                              have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
                              exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(And.left _domain_target), (And.intro (And.left (And.right _domain_target)) (And.right (And.right _domain_target)))⟩)
                            ) x hx, fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain from by
                              intro _preimage_input _preimage_domain
                              obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.C (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) _litex_input) _).mp _preimage_domain
                              rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
                              have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
                              have _domain_target := h_73 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0 _preimage_guard_1
                              have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
                              exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(And.left _domain_target), (And.intro (And.left (And.right _domain_target)) (And.right (And.right _domain_target)))⟩)
                            ) x hx⟩))
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
                              exact h_26 _arg_0 _member_0 (And.left _guard) (And.right _guard))
                          )
                      )
                    exact (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))) _raw_i5) → True := (by
                        rintro _raw_i5 h_199 ⟨h_9, h_10⟩
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_199)
                        have h_199 : Litex.In _value_i5 (Litex.R (M := M)) := h_199
                        have h_9 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  change (¬ (_raw_i5 = (M.number (1 : ℂ))))
                                  exact h_9)
                              )
                          )
                        have h_10 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  change (¬ (_raw_i5 = (M.number (0 : ℂ))))
                                  exact h_10)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ)))))))))
                    exact (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) _raw_i4) → True := (by
                        rintro _raw_i4 h_194 ⟨h_7, h_8⟩
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_194)
                        have h_194 : Litex.In _value_i4 (Litex.R (M := M)) := h_194
                        have h_7 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  change (¬ (_raw_i4 = (M.number (1 : ℂ))))
                                  exact h_7)
                              )
                          )
                        have h_8 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                  exact h_8)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ))))))) _raw_i4) → True := (by
                        rintro _raw_i4 h_194 ⟨h_7, h_8⟩
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_194)
                        have h_194 : Litex.In _value_i4 (Litex.R (M := M)) := h_194
                        have h_7 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  change (¬ (_raw_i4 = (M.number (1 : ℂ))))
                                  exact h_7)
                              )
                          )
                        have h_8 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (by
                                  change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                  exact h_8)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i4 : M.Value) => (((¬ (_raw_i4 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i4 = (M.number (0 : ℂ)))))))))
                      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) h_25))
                  )
                )
            )
          exact (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) _raw_i3) → True := (by
                rintro _raw_i3 h_209 ⟨h_3, h_4⟩
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_209)
                have h_209 : Litex.In _value_i3 (Litex.R (M := M)) := h_209
                have h_3 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          change (¬ (_raw_i3 = (M.number (1 : ℂ))))
                          exact h_3)
                      )
                  )
                have h_4 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          change (¬ (_raw_i3 = (M.number (0 : ℂ))))
                          exact h_4)
                      )
                  )
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i3 : M.Value) => (((¬ (_raw_i3 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i3 = (M.number (0 : ℂ)))))))))
            exact (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))) _raw_i5) → True := (by
                rintro _raw_i5 h_204 ⟨h_9, h_10⟩
                let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_204)
                have h_204 : Litex.In _value_i5 (Litex.R (M := M)) := h_204
                have h_9 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          change (¬ (_raw_i5 = (M.number (1 : ℂ))))
                          exact h_9)
                      )
                  )
                have h_10 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          change (¬ (_raw_i5 = (M.number (0 : ℂ))))
                          exact h_10)
                      )
                  )
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))) _raw_i5) → True := (by
                rintro _raw_i5 h_204 ⟨h_9, h_10⟩
                let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_204)
                have h_204 : Litex.In _value_i5 (Litex.R (M := M)) := h_204
                have h_9 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          change (¬ (_raw_i5 = (M.number (1 : ℂ))))
                          exact h_9)
                      )
                  )
                have h_10 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          change (¬ (_raw_i5 = (M.number (0 : ℂ))))
                          exact h_10)
                      )
                  )
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ)))))))))
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_11))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_function_x5f_membership_x5f_domains_x2f_statement_x2e_lit
