import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_guarded_x5f_from_x5f_epsilon_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v3 v4 v5 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_17 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_20 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
    intro _raw_i2 h_19 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_19)
    have h_19 : Litex.In _value_i2 (Litex.R (M := M)) := h_19
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
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_21 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_22 : Litex.In _value_i4 (Litex.R (M := M))) (h_7 : ∀ (_value_i5 : Litex.Obj (M := M) M.Value) (h_23 : Litex.In _value_i5 (Litex.RPos (M := M))), ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_29 : Litex.In _value_i6 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i7 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i7 (Litex.R (M := M))) => ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ))))), (by
  have h_30 : (M.mem (Litex.denote _value_i6) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i7 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i7 (Litex.R (M := M))) => ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i6 _litex_builder).mp h_29)).choose
        )
    )
  exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i6 _value_i3 (M.real_subset_complex _ h_30) (M.real_subset_complex _ h_21));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i6 _value_i3 h_30 h_21))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i6 _value_i3 (M.real_subset_complex _ h_30) (M.real_subset_complex _ h_21));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i6 _value_i3 h_30 h_21)))) _value_i5))
)) (h_15 : ∀ (_value_i8 : Litex.Obj (M := M) M.Value) (h_1274 : Litex.In _value_i8 (Litex.RPos (M := M))), ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_1278 : Litex.In _value_i9 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_1282 : Litex.In _value_i11 (Litex.R (M := M))) => ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_1285 : Litex.In _value_i10 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_1282 : Litex.In _value_i11 (Litex.R (M := M))) => ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))))) => (by
  have h_1286 : (M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_1282 : Litex.In _value_i11 (Litex.R (M := M))) => ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i10 _litex_builder).mp h_1285)).choose
        )
    )
  exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i10 _value_i3 (M.real_subset_complex _ h_1286) (M.real_subset_complex _ h_21));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i10 _value_i3 h_1286 h_21))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i10 _value_i3 (M.real_subset_complex _ h_1286) (M.real_subset_complex _ h_21));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i10 _value_i3 h_1286 h_21)))) _value_i9))
))) (let _wd_1_0 := _value_i1;
let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_2675 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 _value_i4 (M.real_subset_complex _ h_2675) (M.real_subset_complex _ h_22));
(Litex.abs _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.subInR _value_i12 _value_i4 h_2675 h_22)))) _value_i8));
(by
  have _preimage_target : (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_3089 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 _value_i4 (M.real_subset_complex _ h_3089) (M.real_subset_complex _ h_22));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i12 _value_i4 h_3089 h_22)))) _value_i8))
  exact Litex.IsSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_3089 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 _value_i4 (M.real_subset_complex _ h_3089) (M.real_subset_complex _ h_22));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i12 _value_i4 h_3089 h_22)))) _value_i8))
  exact (Litex.isSet _atomic_wd_1_0))
  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_3504 : Litex.In _value_i14 (Litex.R (M := M))) => ∃ (h_3502 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i14 h_20 h_3504 h_3502) _wd_1_1))
  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
    intro _raw_i2 h_19 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_19)
    have h_19 : Litex.In _value_i2 (Litex.R (M := M)) := h_19
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
    intro _raw_i2 h_19 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_19)
    have h_19 : Litex.In _value_i2 (Litex.R (M := M)) := h_19
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
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_20)))), (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
      intro _raw_i2 h_19 h_1
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_19)
      have h_19 : Litex.In _value_i2 (Litex.R (M := M)) := h_19
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
      intro _raw_i2 h_19 h_1
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_19)
      have h_19 : Litex.In _value_i2 (Litex.R (M := M)) := h_19
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
      intro _raw_i2 h_19 h_1
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_19)
      have h_19 : Litex.In _value_i2 (Litex.R (M := M)) := h_19
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
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_20)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_3993 : Litex.In _value_i3 (Litex.R (M := M)) := h_21
  have h_4000 : Litex.In _value_i4 (Litex.R (M := M)) := h_22
  exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i4) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_20 _Host_i3 _rep_i3 _value_i3 h_21 _Host_i4 _rep_i4 _value_i4 h_22 h_7 h_15
          have h_4010 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
              intro _raw_i2 h_4009 h_1
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
              have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                  h_20
                )
            )
          have h_4011 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_21
                )
            )
          have h_4012 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_22
                )
            )
          have h_18 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_7983 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                          intro _raw_i2 h_4009 h_1
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
                          have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                                  intro _raw_i2 h_4009 h_1
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
                                  have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                              exact h_4010)
                          )
                      )
                    have h_7984 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_7985 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_7984
                          )
                      )
                    have h_7986 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4011
                          )
                      )
                    have h_7987 : Litex.In _value_i4 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4012
                          )
                      )
                    have h_7992 : ∀ {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_8040 : Litex.In _value_i16 (Litex.RPos (M := M))), ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_8046 : Litex.In _value_i17 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_8044 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))))), (by
                      have h_8047 : (M.mem (Litex.denote _value_i17) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_8044 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i17 _litex_builder).mp h_8046)).choose
                            )
                        )
                      exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i17 _value_i3 (M.real_subset_complex _ h_8047) (M.real_subset_complex _ h_7986));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR _value_i17 _value_i3 h_8047 h_7986))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i17 _value_i3 (M.real_subset_complex _ h_8047) (M.real_subset_complex _ h_7986));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR _value_i17 _value_i3 h_8047 h_7986)))) _value_i16))
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i16 _rep_i16 _value_i16 h_8040
                              have h_8041 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRPos_positive _value_i16 h_8040)
                                    )
                                )
                              have h_8042 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_8041)
                                    )
                                )
                              have h_8043 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_8041) _litex_zero.symm)
                                    )
                                )
                              exact (h_7 (Litex.semanticObject (Litex.denote _value_i16) (Litex.isSet _value_i16)) h_8040)
                            )
                          )
                      )
                    have h_7999 : ∀ {_Host_i18 : Type _} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_9890 : Litex.In _value_i18 (Litex.RPos (M := M))), ∃ (_value_i19 : Litex.Obj (M := M) M.Value), ∃ (h_9894 : Litex.In _value_i19 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_9898 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_9901 : Litex.In _value_i20 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_9898 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))))) => (by
                      have h_9902 : (M.mem (Litex.denote _value_i20) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_9898 : Litex.In _value_i2 (Litex.R (M := M))) => ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i20 _litex_builder).mp h_9901)).choose
                            )
                        )
                      exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i20 _value_i3 (M.real_subset_complex _ h_9902) (M.real_subset_complex _ h_7986));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR _value_i20 _value_i3 h_9902 h_7986))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i20 _value_i3 (M.real_subset_complex _ h_9902) (M.real_subset_complex _ h_7986));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR _value_i20 _value_i3 h_9902 h_7986)))) _value_i19))
                    ))) (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_11891 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 _value_i4 (M.real_subset_complex _ h_11891) (M.real_subset_complex _ h_7987));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.subInR _value_i21 _value_i4 h_11891 h_7987)))) _value_i18));
                    (by
                      have _preimage_target : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_12543 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 _value_i4 (M.real_subset_complex _ h_12543) (M.real_subset_complex _ h_7987));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i21 _value_i4 h_12543 h_7987)))) _value_i18))
                      exact Litex.IsSet _atomic_wd_1_0) := (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_12543 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i21 _value_i4 (M.real_subset_complex _ h_12543) (M.real_subset_complex _ h_7987));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i21 _value_i4 h_12543 h_7987)))) _value_i18))
                      exact (Litex.isSet _atomic_wd_1_0))
                      let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_13196 : Litex.In _value_i24 (Litex.R (M := M))) => ∃ (h_13194 : ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ))), Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _value_i24 h_7983 h_13196 h_13194) _wd_1_1))
                      exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                        intro _raw_i2 h_4009 h_1
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
                        have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                        intro _raw_i2 h_4009 h_1
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
                        have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_7983))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i18 _rep_i18 _value_i18 h_9890
                              have h_9891 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i18 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRPos_positive _value_i18 h_9890)
                                    )
                                )
                              have h_9892 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i18 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i18 h_9891)
                                    )
                                )
                              have h_9893 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i18 h_9891) _litex_zero.symm)
                                    )
                                )
                              exact (h_15 (Litex.semanticObject (Litex.denote _value_i18) (Litex.isSet _value_i18)) h_9890)
                            )
                          )
                      )
                    have h_8000 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                                let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                                  intro _raw_i2 h_4009 h_1
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
                                  have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                                  intro _raw_i2 h_4009 h_1
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
                                  have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                                  intro _raw_i2 h_4009 h_1
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
                                  have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_7983)
                                have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_7984
                                have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_7984
                                refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                                intro x hx
                                exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              )
                              have h_13944 : Litex.In _value_i3 (Litex.R (M := M)) := h_7986
                              have h_13951 : Litex.In _value_i4 (Litex.R (M := M)) := h_7987
                              exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i4) from (by
                              let _signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                                intro _raw_i2 h_4009 h_1
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
                                have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                                intro _raw_i2 h_4009 h_1
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
                                have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                                intro _raw_i2 h_4009 h_1
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
                                have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_7983)
                              let _source_domain := (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i2 : M.Value) => ∃ (_ : M.mem _raw_i2 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i2 = (M.number (0 : ℂ))))))
                              have _domain_set : M.isSet _source_domain := (Litex.SetSemantics.sep_isSet (Litex.denote (Litex.R (M := M))) _ (Litex.isSet (Litex.R (M := M))))
                              have _domain_match : _source_domain = _signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
                                intro x
                                change M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _)
                                rw [Litex.SetSemantics.sep_members, Litex.SetSemantics.sep_members]
                                exact ⟨fun ⟨hx, _, hg⟩ => ⟨hx, hg⟩, fun ⟨hx, hg⟩ => ⟨hx, hx, hg⟩⟩
                              let _domain := Litex.semanticObject _source_domain _domain_set
                              have _epsilon_real_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                              let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
                                intro _raw_i2 h_4009 h_1
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
                                have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                                intro _raw_i2 h_4009 h_1
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
                                have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                                intro _raw_i2 h_4009 h_1
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4009)
                                have h_4009 : Litex.In _value_i2 (Litex.R (M := M)) := h_4009
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
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_7983)
                              have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_7984
                              have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_7984
                              refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                              intro x hx
                              exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                            )
                              exact Litex.finiteFunctionLimitOfForall .both _value_i1 _value_i3 _value_i4 _domain _epsilon_real_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_7986 h_7987 h_7992 h_7999
                            ))
                          )
                      )
                    exact h_8000
                  )
                )
            )
          exact h_18
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_guarded_x5f_from_x5f_epsilon_x5f_by_x5f_theorem_x2f_statement_x2e_lit
