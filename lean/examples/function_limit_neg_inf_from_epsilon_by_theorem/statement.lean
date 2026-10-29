import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_neg_x5f_inf_x5f_from_x5f_epsilon_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v3 v4 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_10 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_13 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_12 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12)
    have h_12 : Litex.In _value_i2 (Litex.R (M := M)) := h_12
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_14 : Litex.In _value_i3 (Litex.R (M := M))) (h_3 : ∀ (_value_i4 : Litex.Obj (M := M) M.Value) (h_15 : Litex.In _value_i4 (Litex.R (M := M))), ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_16 : Litex.In _value_i5 (Litex.R (M := M))), Litex.Lt _value_i5 _value_i4) (h_8 : ∀ (_value_i6 : Litex.Obj (M := M) M.Value) (h_44 : Litex.In _value_i6 (Litex.RPos (M := M))), ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_48 : Litex.In _value_i7 (Litex.R (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_49 : Litex.In _value_i8 (Litex.R (M := M))) => Litex.Lt _value_i8 _value_i7)) (let _wd_1_0 := _value_i1;
let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_88 : Litex.In _value_i9 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i9 _value_i3 (M.real_subset_complex _ h_88) (M.real_subset_complex _ h_14));
(Litex.abs _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.subInR _value_i9 _value_i3 h_88 h_14)))) _value_i6));
(by
  have _preimage_target : (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_441 : Litex.In _value_i9 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i9 _value_i3 (M.real_subset_complex _ h_441) (M.real_subset_complex _ h_14));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i9 _value_i3 h_441 h_14)))) _value_i6))
  exact Litex.IsSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_441 : Litex.In _value_i9 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i9 _value_i3 (M.real_subset_complex _ h_441) (M.real_subset_complex _ h_14));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i9 _value_i3 h_441 h_14)))) _value_i6))
  exact (Litex.isSet _atomic_wd_1_0))
  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_794 : Litex.In _value_i11 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i11 h_13 h_794 True.intro) _wd_1_1))
  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_12 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12)
    have h_12 : Litex.In _value_i2 (Litex.R (M := M)) := h_12
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_12 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12)
    have h_12 : Litex.In _value_i2 (Litex.R (M := M)) := h_12
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_13)))), (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_12 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12)
      have h_12 : Litex.In _value_i2 (Litex.R (M := M)) := h_12
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_12 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12)
      have h_12 : Litex.In _value_i2 (Litex.R (M := M)) := h_12
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_12 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12)
      have h_12 : Litex.In _value_i2 (Litex.R (M := M)) := h_12
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_13)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_1214 : Litex.In _value_i3 (Litex.R (M := M)) := h_14
  exact Litex.HasInfiniteFunctionLimit .negative _value_i1 _value_i3) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_13 _Host_i3 _rep_i3 _value_i3 h_14 h_3 h_8
          have h_1222 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_1221 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
              have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          have h_1223 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_14
                )
            )
          have h_11 : Litex.HasInfiniteFunctionLimit .negative _value_i1 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_2423 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_1221 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
                          have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_1221 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
                                  have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                              exact h_1222)
                          )
                      )
                    have h_2424 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_2425 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2424
                          )
                      )
                    have h_2426 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1223
                          )
                      )
                    have h_2429 : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_2462 : Litex.In _value_i13 (Litex.R (M := M))), ∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (h_2463 : Litex.In _value_i14 (Litex.R (M := M))), Litex.Lt _value_i14 _value_i13 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i13 _rep_i13 _value_i13 h_2462
                              exact (h_3 (Litex.semanticObject (Litex.denote _value_i13) (Litex.isSet _value_i13)) h_2462)
                            )
                          )
                      )
                    have h_2434 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_2499 : Litex.In _value_i15 (Litex.RPos (M := M))), ∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_2503 : Litex.In _value_i16 (Litex.R (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_2504 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt _value_i17 _value_i16)) (let _wd_1_0 := _value_i1;
                    let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i18 : Litex.Obj (M := M) M.Value) (h_2547 : Litex.In _value_i18 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i18 _value_i3 (M.real_subset_complex _ h_2547) (M.real_subset_complex _ h_2426));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.subInR _value_i18 _value_i3 h_2547 h_2426)))) _value_i15));
                    (by
                      have _preimage_target : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i18 : Litex.Obj (M := M) M.Value) (h_3076 : Litex.In _value_i18 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i18 _value_i3 (M.real_subset_complex _ h_3076) (M.real_subset_complex _ h_2426));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i18 _value_i3 h_3076 h_2426)))) _value_i15))
                      exact Litex.IsSet _atomic_wd_1_0) := (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i18 : Litex.Obj (M := M) M.Value) (h_3076 : Litex.In _value_i18 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i18 _value_i3 (M.real_subset_complex _ h_3076) (M.real_subset_complex _ h_2426));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i18 _value_i3 h_3076 h_2426)))) _value_i15))
                      exact (Litex.isSet _atomic_wd_1_0))
                      let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_3605 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i21 h_2423 h_3605 True.intro) _wd_1_1))
                      exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_1221 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
                        have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_1221 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
                        have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_2423))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i15 _rep_i15 _value_i15 h_2499
                              have h_2500 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRPos_positive _value_i15 h_2499)
                                    )
                                )
                              have h_2501 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i15 h_2500)
                                    )
                                )
                              have h_2502 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i15 h_2500) _litex_zero.symm)
                                    )
                                )
                              exact (h_8 (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) h_2499)
                            )
                          )
                      )
                    have h_2435 : Litex.HasInfiniteFunctionLimit .negative _value_i1 _value_i3 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                                let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_1221 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
                                  have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                                have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_1221 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
                                  have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_1221 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
                                  have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_2423)
                                have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_2424
                                have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_2424
                                refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                                intro x hx
                                exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              )
                              have h_4221 : Litex.In _value_i3 (Litex.R (M := M)) := h_2426
                              exact Litex.HasInfiniteFunctionLimit .negative _value_i1 _value_i3) from (by
                              let _signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_1221 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
                                have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                              have _member : Litex.In _value_i1 (Litex.fnSet _signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_1221 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
                                have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_1221 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
                                have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_2423)
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
                                intro _raw_i2 h_1221 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
                                have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                              have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_1221 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
                                have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_1221 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1221)
                                have h_1221 : Litex.In _value_i2 (Litex.R (M := M)) := h_1221
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_2423)
                              have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_2424
                              have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_2424
                              refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                              intro x hx
                              exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                            )
                              exact Litex.infiniteFunctionLimitOfForall .negative _value_i1 _value_i3 _domain _epsilon_real_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_2426 h_2429 h_2434
                            ))
                          )
                      )
                    exact h_2435
                  )
                )
            )
          exact h_11
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_neg_x5f_inf_x5f_from_x5f_epsilon_x5f_by_x5f_theorem_x2f_statement_x2e_lit
