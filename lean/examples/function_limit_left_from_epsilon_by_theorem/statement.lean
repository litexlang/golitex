import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_left_x5f_from_x5f_epsilon_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v3 v4 v5 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_14 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_16 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_16)
    have h_16 : Litex.In _value_i2 (Litex.R (M := M)) := h_16
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_19 : Litex.In _value_i4 (Litex.R (M := M))) (h_5 : ∀ (_value_i5 : Litex.Obj (M := M) M.Value) (h_20 : Litex.In _value_i5 (Litex.RPos (M := M))), ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_24 : Litex.In _value_i6 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i3 _value_i6 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_24))) ∧ (Litex.Lt (Litex.sub _value_i3 _value_i6 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_24)) _value_i5))) (h_12 : ∀ (_value_i7 : Litex.Obj (M := M) M.Value) (h_464 : Litex.In _value_i7 (Litex.RPos (M := M))), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_468 : Litex.In _value_i8 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_472 : Litex.In _value_i9 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i3 _value_i9 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_472))) ∧ (Litex.Lt (Litex.sub _value_i3 _value_i9 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_472)) _value_i8)))) (let _wd_1_0 := _value_i1;
let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_988 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_988) (M.real_subset_complex _ h_19));
(Litex.abs _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.subInR _value_i10 _value_i4 h_988 h_19)))) _value_i7));
(by
  have _preimage_target : (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_1402 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_1402) (M.real_subset_complex _ h_19));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i10 _value_i4 h_1402 h_19)))) _value_i7))
  exact Litex.IsSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_1402 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_1402) (M.real_subset_complex _ h_19));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i10 _value_i4 h_1402 h_19)))) _value_i7))
  exact (Litex.isSet _atomic_wd_1_0))
  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_1816 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i12 h_17 h_1816 True.intro) _wd_1_1))
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
  have h_2298 : Litex.In _value_i3 (Litex.R (M := M)) := h_18
  have h_2305 : Litex.In _value_i4 (Litex.R (M := M)) := h_19
  exact Litex.HasFiniteFunctionLimit .left _value_i1 _value_i3 _value_i4) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i3 _rep_i3 _value_i3 h_18 _Host_i4 _rep_i4 _value_i4 h_19 h_5 h_12
          have h_2315 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_2314 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
              have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_17
                )
            )
          have h_2316 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_18
                )
            )
          have h_2317 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_19
                )
            )
          have h_15 : Litex.HasFiniteFunctionLimit .left _value_i1 _value_i3 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_4596 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_2314 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
                          have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_2314 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
                                  have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                              exact h_2315)
                          )
                      )
                    have h_4597 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_4598 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4597
                          )
                      )
                    have h_4599 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2316
                          )
                      )
                    have h_4600 : Litex.In _value_i4 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2317
                          )
                      )
                    have h_4605 : ∀ {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_4652 : Litex.In _value_i14 (Litex.RPos (M := M))), ∃ (_value_i15 : Litex.Obj (M := M) M.Value), ∃ (h_4656 : Litex.In _value_i15 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i3 _value_i15 (M.real_subset_complex _ h_4599) (M.real_subset_complex _ h_4656))) ∧ (Litex.Lt (Litex.sub _value_i3 _value_i15 (M.real_subset_complex _ h_4599) (M.real_subset_complex _ h_4656)) _value_i14)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i14 _rep_i14 _value_i14 h_4652
                              have h_4653 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRPos_positive _value_i14 h_4652)
                                    )
                                )
                              have h_4654 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_4653)
                                    )
                                )
                              have h_4655 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_4653) _litex_zero.symm)
                                    )
                                )
                              exact (h_5 (Litex.semanticObject (Litex.denote _value_i14) (Litex.isSet _value_i14)) h_4652)
                            )
                          )
                      )
                    have h_4612 : ∀ {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_5356 : Litex.In _value_i16 (Litex.RPos (M := M))), ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_5360 : Litex.In _value_i17 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i18 : Litex.Obj (M := M) M.Value) (h_5364 : Litex.In _value_i18 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i3 _value_i18 (M.real_subset_complex _ h_4599) (M.real_subset_complex _ h_5364))) ∧ (Litex.Lt (Litex.sub _value_i3 _value_i18 (M.real_subset_complex _ h_4599) (M.real_subset_complex _ h_5364)) _value_i17)))) (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_6132 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i4 (M.real_subset_complex _ h_6132) (M.real_subset_complex _ h_4600));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.subInR _value_i19 _value_i4 h_6132 h_4600)))) _value_i16));
                    (by
                      have _preimage_target : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_6784 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i4 (M.real_subset_complex _ h_6784) (M.real_subset_complex _ h_4600));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i19 _value_i4 h_6784 h_4600)))) _value_i16))
                      exact Litex.IsSet _atomic_wd_1_0) := (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_6784 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i19 _value_i4 (M.real_subset_complex _ h_6784) (M.real_subset_complex _ h_4600));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i19 _value_i4 h_6784 h_4600)))) _value_i16))
                      exact (Litex.isSet _atomic_wd_1_0))
                      let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i22 : Litex.Obj (M := M) M.Value) (h_7436 : Litex.In _value_i22 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i22 h_4596 h_7436 True.intro) _wd_1_1))
                      exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_2314 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
                        have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_2314 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
                        have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_4596))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i16 _rep_i16 _value_i16 h_5356
                              have h_5357 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRPos_positive _value_i16 h_5356)
                                    )
                                )
                              have h_5358 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i16 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i16 h_5357)
                                    )
                                )
                              have h_5359 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i16 h_5357) _litex_zero.symm)
                                    )
                                )
                              exact (h_12 (Litex.semanticObject (Litex.denote _value_i16) (Litex.isSet _value_i16)) h_5356)
                            )
                          )
                      )
                    have h_4613 : Litex.HasFiniteFunctionLimit .left _value_i1 _value_i3 _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                                let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_2314 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
                                  have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                                have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_2314 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
                                  have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_2314 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
                                  have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_4596)
                                have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_4597
                                have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_4597
                                refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                                intro x hx
                                exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              )
                              have h_8177 : Litex.In _value_i3 (Litex.R (M := M)) := h_4599
                              have h_8184 : Litex.In _value_i4 (Litex.R (M := M)) := h_4600
                              exact Litex.HasFiniteFunctionLimit .left _value_i1 _value_i3 _value_i4) from (by
                              let _signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_2314 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
                                have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                              have _member : Litex.In _value_i1 (Litex.fnSet _signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_2314 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
                                have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_2314 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
                                have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_4596)
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
                                intro _raw_i2 h_2314 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
                                have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                              have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_2314 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
                                have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_2314 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2314)
                                have h_2314 : Litex.In _value_i2 (Litex.R (M := M)) := h_2314
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_4596)
                              have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_4597
                              have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_4597
                              refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                              intro x hx
                              exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                            )
                              exact Litex.finiteFunctionLimitOfForall .left _value_i1 _value_i3 _value_i4 _domain _epsilon_real_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_4599 h_4600 h_4605 h_4612
                            ))
                          )
                      )
                    exact h_4613
                  )
                )
            )
          exact h_15
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_left_x5f_from_x5f_epsilon_x5f_by_x5f_theorem_x2f_statement_x2e_lit
