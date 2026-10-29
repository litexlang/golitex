import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_right_x5f_local_x5f_equal_x2f_statement_x2e_lit

universe u v1 v2 v4 v5 v6 v7 v9
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_13 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_14 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i3 (Litex.R (M := M)) := h_14
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_16 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_14 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i3 (Litex.R (M := M)) := h_14
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_17 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_18 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_19 : Litex.In _value_i6 (Litex.RPos (M := M))) (h_1 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_14 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i3 (Litex.R (M := M)) := h_14
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_14 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i3 (Litex.R (M := M)) := h_14
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_14 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i3 (Litex.R (M := M)) := h_14
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_15)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_25 : Litex.In _value_i4 (Litex.R (M := M)) := h_17
  have h_34 : Litex.In _value_i5 (Litex.R (M := M)) := h_18
  exact Litex.HasFiniteFunctionLimit .right _value_i1 _value_i4 _value_i5)) (h_6 : ∀ (_value_i7 : Litex.Obj (M := M) M.Value) (h_45 : Litex.In _value_i7 (Litex.RPos (M := M))), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_49 : Litex.In _value_i8 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i8 _value_i4 (M.real_subset_complex _ h_49) (M.real_subset_complex _ h_17))) ∧ (Litex.Lt (Litex.sub _value_i8 _value_i4 (M.real_subset_complex _ h_49) (M.real_subset_complex _ h_17)) _value_i7))) (h_11 : ∀ (_value_i9 : Litex.Obj (M := M) M.Value) (h_1117 : Litex.In _value_i9 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_621 : Litex.In _value_i10 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_621) (M.real_subset_complex _ h_17))) ∧ (Litex.Lt (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_621) (M.real_subset_complex _ h_17)) _value_i6))))), (by
  have h_1118 : (M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_621 : Litex.In _value_i10 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_621) (M.real_subset_complex _ h_17))) ∧ (Litex.Lt (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_621) (M.real_subset_complex _ h_17)) _value_i6)))); (Litex.inSetBuilderObj_iff _value_i9 _litex_builder).mp h_1117)).choose
        )
    )
  exact (by
    let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i2 _value_i9 h_16 h_1118 True.intro)
    let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i1 _value_i9 h_15 h_1118 True.intro)
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
)), (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_14 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i3 (Litex.R (M := M)) := h_14
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_14 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i3 (Litex.R (M := M)) := h_14
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_14 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i3 (Litex.R (M := M)) := h_14
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_16)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_1143 : Litex.In _value_i4 (Litex.R (M := M)) := h_17
  have h_1152 : Litex.In _value_i5 (Litex.R (M := M)) := h_18
  exact Litex.HasFiniteFunctionLimit .right _value_i2 _value_i4 _value_i5) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15 _Host_i2 _rep_i2 _value_i2 h_16 _Host_i4 _rep_i4 _value_i4 h_17 _Host_i5 _rep_i5 _value_i5 h_18 _Host_i6 _rep_i6 _value_i6 h_19 h_1 h_6 h_11
          have h_20 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i6 h_19)
                )
            )
          have h_21 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i6 h_20)
                )
            )
          have h_22 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i6 h_20) _litex_zero.symm)
                )
            )
          have h_1164 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_1163 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1163)
              have h_1163 : Litex.In _value_i3 (Litex.R (M := M)) := h_1163
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          have h_1165 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_1163 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1163)
              have h_1163 : Litex.In _value_i3 (Litex.R (M := M)) := h_1163
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_16
                )
            )
          have h_1166 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_17
                )
            )
          have h_1167 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_18
                )
            )
          have h_1168 : Litex.In _value_i6 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_19
                )
            )
          have h_1169 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i6 h_1168)
                )
            )
          have h_1170 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i6 h_1169)
                )
            )
          have h_1171 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i6 h_1169) _litex_zero.symm)
                )
            )
          have h_2313 : Litex.HasFiniteFunctionLimit .right _value_i2 _value_i4 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_2291 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                          intro _raw_i3 h_1163 _
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1163)
                          have h_1163 : Litex.In _value_i3 (Litex.R (M := M)) := h_1163
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_1163 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1163)
                                  have h_1163 : Litex.In _value_i3 (Litex.R (M := M)) := h_1163
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                              exact h_1164)
                          )
                      )
                    have h_2292 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_2293 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2292
                          )
                      )
                    have h_2294 : Litex.In _value_i4 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1166
                          )
                      )
                    have h_2297 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                          intro _raw_i3 h_1163 _
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1163)
                          have h_1163 : Litex.In _value_i3 (Litex.R (M := M)) := h_1163
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_1163 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1163)
                                  have h_1163 : Litex.In _value_i3 (Litex.R (M := M)) := h_1163
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                              exact h_1165)
                          )
                      )
                    have h_2298 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2292
                          )
                      )
                    have h_2299 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2292
                          )
                      )
                    have h_2300 : Litex.HasFiniteFunctionLimit .right _value_i1 _value_i4 _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_2301 : Litex.In _value_i6 (Litex.RPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1168
                          )
                      )
                    have h_2386 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i6 h_2301)
                          )
                      )
                    have h_2387 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i6 h_2386)
                          )
                      )
                    have h_2388 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i6 h_2386) _litex_zero.symm)
                          )
                      )
                    have h_2306 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_2393 : Litex.In _value_i12 (Litex.RPos (M := M))), ∃ (_value_i13 : Litex.Obj (M := M) M.Value), ∃ (h_2397 : Litex.In _value_i13 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i13 _value_i4 (M.real_subset_complex _ h_2397) (M.real_subset_complex _ h_2294))) ∧ (Litex.Lt (Litex.sub _value_i13 _value_i4 (M.real_subset_complex _ h_2397) (M.real_subset_complex _ h_2294)) _value_i12)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i12 _rep_i12 _value_i12 h_2393
                              have h_2394 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRPos_positive _value_i12 h_2393)
                                    )
                                )
                              have h_2395 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i12 h_2394)
                                    )
                                )
                              have h_2396 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i12 h_2394) _litex_zero.symm)
                                    )
                                )
                              exact (h_6 (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) h_2393)
                            )
                          )
                      )
                    have h_2310 : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_3369 : Litex.In _value_i14 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294))) ∧ (Litex.Lt (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294)) _value_i6))))
                      exact Litex.Subset _atomic_wd_1_0 (Litex.R (M := M))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_3369 : Litex.In _value_i14 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294))) ∧ (Litex.Lt (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294)) _value_i6))))
                              exact (by
                                let _set := _atomic_wd_1_0
                                exact Litex.setBuilderSubset _set.val.bound _set.val.predicate))
                          )
                      )
                    have h_2312 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_4282 : Litex.In _value_i15 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_3369 : Litex.In _value_i14 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294))) ∧ (Litex.Lt (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294)) _value_i6))))), (by
                      have h_4283 : (M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_3369 : Litex.In _value_i14 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294))) ∧ (Litex.Lt (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294)) _value_i6)))); (Litex.inSetBuilderObj_iff _value_i15 _litex_builder).mp h_4282)).choose
                            )
                        )
                      exact Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i2 _value_i15 h_2297 h_4283 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i1 _value_i15 h_2291 h_4283 True.intro)
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i15 _rep_i15 _value_i15 h_4282
                              have h_4283 : (M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_3369 : Litex.In _value_i14 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294))) ∧ (Litex.Lt (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294)) _value_i6)))); (Litex.inSetBuilderObj_iff _value_i15 _litex_builder).mp h_4282)).choose
                                    )
                                )
                              have h_4286 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (M.subValue (Litex.denote _value_i15) (Litex.denote _value_i4)) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (M.subValue (Litex.denote _value_i15) (Litex.denote _value_i4)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i6) = M.number (_s : ℂ) ∧ _r < _s))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_3369 : Litex.In _value_i14 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294))) ∧ (Litex.Lt (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294)) _value_i6)))); (Litex.inSetBuilderObj_iff _value_i15 _litex_builder).mp h_4282)).choose_spec
                                    )
                                )
                              have h_4284 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_3369 : Litex.In _value_i14 (Litex.R (M := M))) => (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294))) (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) h_4283) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.left h_4286)
                                    )
                                )
                              have h_4285 : Litex.Lt ((fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_3369 : Litex.In _value_i14 (Litex.R (M := M))) => (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_3369) (M.real_subset_complex _ h_2294))) (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) h_4283) _value_i6 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.right h_4286)
                                    )
                                )
                              exact (h_11 (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) h_4282)
                            )
                          )
                      )
                    exact (show (by
                    have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
                      let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                        intro _raw_i3 h_1163 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1163)
                        have h_1163 : Litex.In _value_i3 (Litex.R (M := M)) := h_1163
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                      have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                        intro _raw_i3 h_1163 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1163)
                        have h_1163 : Litex.In _value_i3 (Litex.R (M := M)) := h_1163
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                        intro _raw_i3 h_1163 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1163)
                        have h_1163 : Litex.In _value_i3 (Litex.R (M := M)) := h_1163
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_2297)
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_2292
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_2292
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    )
                    have h_4317 : Litex.In _value_i4 (Litex.R (M := M)) := h_2294
                    have h_4324 : Litex.In _value_i5 (Litex.R (M := M)) := h_1167
                    exact Litex.HasFiniteFunctionLimit .right _value_i2 _value_i4 _value_i5) from (by
                    let _law0_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                      intro _raw_i3 h_1163 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1163)
                      have h_1163 : Litex.In _value_i3 (Litex.R (M := M)) := h_1163
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                    have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_2291
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
                      refine ⟨_law0_signature, _law0_member, ?_, h_2293⟩
                      intro x hx
                      exact h_2292 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                    let _law1_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                      intro _raw_i3 h_1163 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1163)
                      have h_1163 : Litex.In _value_i3 (Litex.R (M := M)) := h_1163
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                    have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_2297
                    let _law1_source_domain := (M.standard Litex.StandardSetValue.real)
                    have _law1_domain_set : M.isSet _law1_source_domain := (Litex.isSet (Litex.R (M := M)))
                    have _law1_domain_match : _law1_source_domain = _law1_signature.domain := by
                      apply Litex.SetSemantics.ext _ _ _law1_domain_set _law1_signature.domain_isSet
                      intro x
                      change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
                      rw [Litex.SetSemantics.sep_members]
                      exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                    let _law1_domain := Litex.semanticObject _law1_source_domain _law1_domain_set
                    have _law_real_1 : Litex.RealFunctionValue M (Litex.denote _value_i2) := by
                      refine ⟨_law1_signature, _law1_member, ?_, h_2299⟩
                      intro x hx
                      exact h_2298 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                    exact Litex.finiteFunctionLimitLocalEqual .right (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i4) (Litex.denote _value_i5) (Litex.denote _law1_domain) _value_i6 h_2301 _law_real_1 _law_domain_1 h_2300 h_2306 (by
                      intro input hinput
                      have _member : M.mem input (Litex.denote _law0_domain) := h_2310 input hinput
                      rw [_law_domain_0] at _member
                      exact _member
                    ) (by
                      intro input hinput
                      exact h_2312 (Litex.semanticObject input (M.member_isSet hinput)) hinput
                    )
                  ))
                  )
                )
            )
          exact h_2313
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_right_x5f_local_x5f_equal_x2f_statement_x2e_lit
