import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_at_x5f_from_x5f_epsilon_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v3 v4 v5 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_14 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_16 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_16)
    have h_16 : Litex.In _value_i2 (Litex.R (M := M)) := h_16
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_19 : Litex.In _value_i4 (Litex.R (M := M))) (h_5 : ∀ (_value_i5 : Litex.Obj (M := M) M.Value) (h_20 : Litex.In _value_i5 (Litex.RPos (M := M))), ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_24 : Litex.In _value_i6 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i6 _value_i3 (M.real_subset_complex _ h_24) (M.real_subset_complex _ h_18));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i6 _value_i3 h_24 h_18))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i6 _value_i3 (M.real_subset_complex _ h_24) (M.real_subset_complex _ h_18));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i6 _value_i3 h_24 h_18)))) _value_i5))) (h_12 : ∀ (_value_i7 : Litex.Obj (M := M) M.Value) (h_905 : Litex.In _value_i7 (Litex.RPos (M := M))), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_909 : Litex.In _value_i8 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_913 : Litex.In _value_i9 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i9 _value_i3 (M.real_subset_complex _ h_913) (M.real_subset_complex _ h_18));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i9 _value_i3 h_913 h_18))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i9 _value_i3 (M.real_subset_complex _ h_913) (M.real_subset_complex _ h_18));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i9 _value_i3 h_913 h_18)))) _value_i8)))) (let _wd_1_0 := _value_i1;
let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_1939 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_1939) (M.real_subset_complex _ h_19));
(Litex.abs _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.subInR _value_i10 _value_i4 h_1939 h_19)))) _value_i7));
(by
  have _preimage_target : (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_2353 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_2353) (M.real_subset_complex _ h_19));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i10 _value_i4 h_2353 h_19)))) _value_i7))
  exact Litex.IsSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_2353 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_2353) (M.real_subset_complex _ h_19));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i10 _value_i4 h_2353 h_19)))) _value_i7))
  exact (Litex.isSet _atomic_wd_1_0))
  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_2767 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i12 h_17 h_2767 True.intro) _wd_1_1))
  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_16 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_16)
    have h_16 : Litex.In _value_i2 (Litex.R (M := M)) := h_16
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_16 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_16)
    have h_16 : Litex.In _value_i2 (Litex.R (M := M)) := h_16
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_17)))), (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_16 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_16)
      have h_16 : Litex.In _value_i2 (Litex.R (M := M)) := h_16
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_16 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_16)
      have h_16 : Litex.In _value_i2 (Litex.R (M := M)) := h_16
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_16 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_16)
      have h_16 : Litex.In _value_i2 (Litex.R (M := M)) := h_16
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_17)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_3249 : Litex.In _value_i3 (Litex.R (M := M)) := h_18
  have h_3256 : Litex.In _value_i4 (Litex.R (M := M)) := h_19
  exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i4) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i3 _rep_i3 _value_i3 h_18 _Host_i4 _rep_i4 _value_i4 h_19 h_5 h_12
          have h_3266 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_3265 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
              have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_17
                )
            )
          have h_3267 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_18
                )
            )
          have h_3268 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_19
                )
            )
          have h_15 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_6498 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_3265 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                          have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_3265 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                                  have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                              exact h_3266)
                          )
                      )
                    have h_6499 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_6500 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_6499
                          )
                      )
                    have h_6501 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3267
                          )
                      )
                    have h_6502 : Litex.In _value_i4 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3268
                          )
                      )
                    have h_6507 : ∀ {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_6554 : Litex.In _value_i14 (Litex.RPos (M := M))), ∃ (_value_i15 : Litex.Obj (M := M) M.Value), ∃ (h_6558 : Litex.In _value_i15 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i15 _value_i3 (M.real_subset_complex _ h_6558) (M.real_subset_complex _ h_6501));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.subInR _value_i15 _value_i3 h_6558 h_6501))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i15 _value_i3 (M.real_subset_complex _ h_6558) (M.real_subset_complex _ h_6501));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.subInR _value_i15 _value_i3 h_6558 h_6501)))) _value_i14)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i14 _rep_i14 _value_i14 h_6554
                              have h_6555 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRPos_positive _value_i14 h_6554)
                                    )
                                )
                              have h_6556 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_6555)
                                    )
                                )
                              have h_6557 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_6555) _litex_zero.symm)
                                    )
                                )
                              exact (h_5 (Litex.semanticObject (Litex.denote _value_i14) (Litex.isSet _value_i14)) h_6554)
                            )
                          )
                      )
                    have h_6514 : ∀ {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_8017 : Litex.In _value_i16 (Litex.RPos (M := M))), ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_8021 : Litex.In _value_i17 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i18 : Litex.Obj (M := M) M.Value) (h_8025 : Litex.In _value_i18 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i18 _value_i3 (M.real_subset_complex _ h_8025) (M.real_subset_complex _ h_6501));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.subInR _value_i18 _value_i3 h_8025 h_6501))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i18 _value_i3 (M.real_subset_complex _ h_8025) (M.real_subset_complex _ h_6501));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.subInR _value_i18 _value_i3 h_8025 h_6501)))) _value_i17)))) (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_9633 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i4 (M.real_subset_complex _ h_9633) (M.real_subset_complex _ h_6502));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.subInR _value_i19 _value_i4 h_9633 h_6502)))) _value_i16));
                    (by
                      have _preimage_target : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_10285 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i4 (M.real_subset_complex _ h_10285) (M.real_subset_complex _ h_6502));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i19 _value_i4 h_10285 h_6502)))) _value_i16))
                      exact Litex.IsSet _atomic_wd_1_0) := (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_10285 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i4 (M.real_subset_complex _ h_10285) (M.real_subset_complex _ h_6502));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i19 _value_i4 h_10285 h_6502)))) _value_i16))
                      exact (Litex.isSet _atomic_wd_1_0))
                      let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i22 : Litex.Obj (M := M) M.Value) (h_10937 : Litex.In _value_i22 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i22 h_6498 h_10937 True.intro) _wd_1_1))
                      exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_3265 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                        have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_3265 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                        have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_6498))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i16 _rep_i16 _value_i16 h_8017
                              have h_8018 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRPos_positive _value_i16 h_8017)
                                    )
                                )
                              have h_8019 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_8018)
                                    )
                                )
                              have h_8020 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_8018) _litex_zero.symm)
                                    )
                                )
                              exact (h_12 (Litex.semanticObject (Litex.denote _value_i16) (Litex.isSet _value_i16)) h_8017)
                            )
                          )
                      )
                    have h_6515 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                                let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_3265 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                                  have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                                have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_3265 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                                  have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_3265 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                                  have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_6498)
                                have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_6499
                                have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_6499
                                refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                                intro x hx
                                exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              )
                              have h_11678 : Litex.In _value_i3 (Litex.R (M := M)) := h_6501
                              have h_11685 : Litex.In _value_i4 (Litex.R (M := M)) := h_6502
                              exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i4) from (by
                              let _signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_3265 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                                have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                              have _member : Litex.In _value_i1 (Litex.fnSet _signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_3265 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                                have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_3265 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                                have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_6498)
                              let _source_domain := (M.standard Litex.StandardSetValue.real)
                              have _domain_set : M.isSet _source_domain := (Litex.isSet (Litex.R (M := M)))
                              have _domain_match : _source_domain = _signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
                                intro x
                                change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
                                rw [Litex.SetSemantics.sep_members]
                                exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                              let _domain := Litex.semanticObject _source_domain _domain_set
                              have _epsilon_real_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                              let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_3265 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                                have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                              have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_3265 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                                have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_3265 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3265)
                                have h_3265 : Litex.In _value_i2 (Litex.R (M := M)) := h_3265
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_6498)
                              have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_6499
                              have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_6499
                              refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                              intro x hx
                              exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                            )
                              exact Litex.finiteFunctionLimitOfForall .both _value_i1 _value_i3 _value_i4 _domain _epsilon_real_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_6501 h_6502 h_6507 h_6514
                            ))
                          )
                      )
                    exact h_6515
                  )
                )
            )
          exact h_15
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_at_x5f_from_x5f_epsilon_x5f_by_x5f_theorem_x2f_statement_x2e_lit
