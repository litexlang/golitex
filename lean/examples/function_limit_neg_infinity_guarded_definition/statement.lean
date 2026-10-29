import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_neg_x5f_infinity_x5f_guarded_x5f_definition_x2f_statement_x2e_lit

universe u v1 v3 v4 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_13 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
    intro _raw_i2 h_15 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i2 (Litex.R (M := M)) := h_15
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
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_17 : Litex.In _value_i3 (Litex.R (M := M))) (h_5 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_18 : Litex.In _value_i4 (Litex.R (M := M))), ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_20 : Litex.In _value_i5 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_19 : Litex.In _value_i6 (Litex.R (M := M))) => ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))))), Litex.Lt _value_i5 _value_i4) (h_11 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_62 : Litex.In _value_i7 (Litex.RPos (M := M))), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_66 : Litex.In _value_i8 (Litex.R (M := M))), Litex.Subset (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_67 : Litex.In _value_i10 (Litex.R (M := M))) => ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_69 : Litex.In _value_i9 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_67 : Litex.In _value_i10 (Litex.R (M := M))) => ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ))))) => Litex.Lt _value_i9 _value_i8)) (let _wd_1_0 := _value_i1;
let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_122 : Litex.In _value_i11 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i11 _value_i3 (M.real_subset_complex _ h_122) (M.real_subset_complex _ h_17));
(Litex.abs _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.subInR _value_i11 _value_i3 h_122 h_17)))) _value_i7));
(by
  have _preimage_target : (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_475 : Litex.In _value_i11 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i11 _value_i3 (M.real_subset_complex _ h_475) (M.real_subset_complex _ h_17));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i11 _value_i3 h_475 h_17)))) _value_i7))
  exact Litex.IsSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_475 : Litex.In _value_i11 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i11 _value_i3 (M.real_subset_complex _ h_475) (M.real_subset_complex _ h_17));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i11 _value_i3 h_475 h_17)))) _value_i7))
  exact (Litex.isSet _atomic_wd_1_0))
  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_829 : Litex.In _value_i13 (Litex.R (M := M))) => ∃ (h_827 : ¬ Litex.Same _value_i13 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i13 h_16 h_829 h_827) _wd_1_1))
  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
    intro _raw_i2 h_15 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i2 (Litex.R (M := M)) := h_15
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
    intro _raw_i2 h_15 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i2 (Litex.R (M := M)) := h_15
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
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_16)))), (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
      intro _raw_i2 h_15 h_1
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_15)
      have h_15 : Litex.In _value_i2 (Litex.R (M := M)) := h_15
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
      intro _raw_i2 h_15 h_1
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_15)
      have h_15 : Litex.In _value_i2 (Litex.R (M := M)) := h_15
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
      intro _raw_i2 h_15 h_1
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_15)
      have h_15 : Litex.In _value_i2 (Litex.R (M := M)) := h_15
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
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_16)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_1255 : Litex.In _value_i3 (Litex.R (M := M)) := h_17
  exact Litex.HasInfiniteFunctionLimit .negative _value_i1 _value_i3) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i3 _rep_i3 _value_i3 h_17 h_5 h_11
          have h_1263 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
              intro _raw_i2 h_1262 h_1
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1262)
              have h_1262 : Litex.In _value_i2 (Litex.R (M := M)) := h_1262
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
                  h_16
                )
            )
          have h_1264 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_17
                )
            )
          have h_14 : (by
            have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
              let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                intro _raw_i2 h_1262 h_1
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1262)
                have h_1262 : Litex.In _value_i2 (Litex.R (M := M)) := h_1262
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
                intro _raw_i2 h_1262 h_1
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1262)
                have h_1262 : Litex.In _value_i2 (Litex.R (M := M)) := h_1262
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
                intro _raw_i2 h_1262 h_1
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1262)
                have h_1262 : Litex.In _value_i2 (Litex.R (M := M)) := h_1262
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
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_1263)
              have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
              have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
              refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
              intro x hx
              exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
            )
            have h_3764 : Litex.In _value_i3 (Litex.R (M := M)) := h_1264
            exact Litex.HasInfiniteFunctionLimit .negative _value_i1 _value_i3) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                      let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                        intro _raw_i2 h_1262 h_1
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1262)
                        have h_1262 : Litex.In _value_i2 (Litex.R (M := M)) := h_1262
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
                        intro _raw_i2 h_1262 h_1
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1262)
                        have h_1262 : Litex.In _value_i2 (Litex.R (M := M)) := h_1262
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
                        intro _raw_i2 h_1262 h_1
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1262)
                        have h_1262 : Litex.In _value_i2 (Litex.R (M := M)) := h_1262
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
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_1263)
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    )
                    have h_3764 : Litex.In _value_i3 (Litex.R (M := M)) := h_1264
                    exact (by
                      let _signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                        intro _raw_i2 h_1262 h_1
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1262)
                        have h_1262 : Litex.In _value_i2 (Litex.R (M := M)) := h_1262
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
                        intro _raw_i2 h_1262 h_1
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1262)
                        have h_1262 : Litex.In _value_i2 (Litex.R (M := M)) := h_1262
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
                        intro _raw_i2 h_1262 h_1
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1262)
                        have h_1262 : Litex.In _value_i2 (Litex.R (M := M)) := h_1262
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
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_1263)
                      let _source_domain := (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i2 : M.Value) => ∃ (_ : M.mem _raw_i2 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i2 = (M.number (0 : ℂ))))))
                      have _domain_set : M.isSet _source_domain := (Litex.SetSemantics.sep_isSet (Litex.denote (Litex.R (M := M))) _ (Litex.isSet (Litex.R (M := M))))
                      have _domain_match : _source_domain = _signature.domain := by
                        apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
                        intro x
                        change M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _)
                        rw [Litex.SetSemantics.sep_members, Litex.SetSemantics.sep_members]
                        exact ⟨fun ⟨hx, _, hg⟩ => ⟨hx, hg⟩, fun ⟨hx, hg⟩ => ⟨hx, hx, hg⟩⟩
                      let _domain := Litex.semanticObject _source_domain _domain_set
                      exact Litex.infiniteFunctionLimitOfForall .negative _value_i1 _value_i3 _domain _function_limit_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_3764 (show ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_2522 : Litex.In _value_i15 (Litex.R (M := M))), ∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_2524 : Litex.In _value_i16 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2523 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))))), Litex.Lt _value_i16 _value_i15 from (by
                      intro _Host_i15 _rep_i15 _value_i15 h_2522
                      exact (h_5 _value_i15 h_2522)
                    )) (show ∀ {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_2571 : Litex.In _value_i17 (Litex.RPos (M := M))), ∃ (_value_i18 : Litex.Obj (M := M) M.Value), ∃ (h_2575 : Litex.In _value_i18 (Litex.R (M := M))), Litex.Subset (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2576 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_2578 : Litex.In _value_i19 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_2576 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))))) => Litex.Lt _value_i19 _value_i18)) (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_2631 : Litex.In _value_i20 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i20 _value_i3 (M.real_subset_complex _ h_2631) (M.real_subset_complex _ h_1264));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_2_0 := _wd_2_0
                      exact (Litex.subInR _value_i20 _value_i3 h_2631 h_1264)))) _value_i17));
                    (by
                      have _preimage_target : (by
                      let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_2984 : Litex.In _value_i20 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i20 _value_i3 (M.real_subset_complex _ h_2984) (M.real_subset_complex _ h_1264));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_3_0 := _wd_2_0
                        exact (Litex.subInR _value_i20 _value_i3 h_2984 h_1264)))) _value_i17))
                      exact Litex.IsSet _atomic_wd_2_0) := (by
                      let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_2984 : Litex.In _value_i20 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i20 _value_i3 (M.real_subset_complex _ h_2984) (M.real_subset_complex _ h_1264));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_3_0 := _wd_2_0
                        exact (Litex.subInR _value_i20 _value_i3 h_2984 h_1264)))) _value_i17))
                      exact (Litex.isSet _atomic_wd_2_0))
                      let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_3338 : Litex.In _value_i21 (Litex.R (M := M))) => ∃ (h_3336 : ¬ Litex.Same _value_i21 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i21 h_1263 h_3338 h_3336) _wd_1_1))
                      exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                        intro _raw_i2 h_1262 h_1
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1262)
                        have h_1262 : Litex.In _value_i2 (Litex.R (M := M)) := h_1262
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
                        intro _raw_i2 h_1262 h_1
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1262)
                        have h_1262 : Litex.In _value_i2 (Litex.R (M := M)) := h_1262
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
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_1263))) from (by
                      intro _Host_i17 _rep_i17 _value_i17 h_2571
                      have h_2572 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inRPos_positive _value_i17 h_2571)
                            )
                        )
                      have h_2573 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.ltToLe (Litex.number (M := M) 0) _value_i17 h_2572)
                            )
                        )
                      have h_2574 : ¬ Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i17 h_2572) _litex_zero.symm)
                            )
                        )
                      exact (h_11 _value_i17 h_2571)
                    ))
                    ))
                )
            )
          exact h_14
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_neg_x5f_infinity_x5f_guarded_x5f_definition_x2f_statement_x2e_lit
