import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_at_x5f_local_x5f_equal_x2f_statement_x2e_lit

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
  exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i4 _value_i5)) (h_6 : ∀ (_value_i7 : Litex.Obj (M := M) M.Value) (h_45 : Litex.In _value_i7 (Litex.RPos (M := M))), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_49 : Litex.In _value_i8 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i8 _value_i4 (M.real_subset_complex _ h_49) (M.real_subset_complex _ h_17));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i8 _value_i4 h_49 h_17))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i8 _value_i4 (M.real_subset_complex _ h_49) (M.real_subset_complex _ h_17));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i8 _value_i4 h_49 h_17)))) _value_i7))) (h_11 : ∀ (_value_i9 : Litex.Obj (M := M) M.Value) (h_2188 : Litex.In _value_i9 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_1191 : Litex.In _value_i10 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_1191) (M.real_subset_complex _ h_17));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i10 _value_i4 h_1191 h_17))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_1191) (M.real_subset_complex _ h_17));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i10 _value_i4 h_1191 h_17)))) _value_i6))))), (by
  have h_2189 : (M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_1191 : Litex.In _value_i10 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_1191) (M.real_subset_complex _ h_17));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i10 _value_i4 h_1191 h_17))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i10 _value_i4 (M.real_subset_complex _ h_1191) (M.real_subset_complex _ h_17));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i10 _value_i4 h_1191 h_17)))) _value_i6)))); (Litex.inSetBuilderObj_iff _value_i9 _litex_builder).mp h_2188)).choose
        )
    )
  exact (by
    let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i2 _value_i9 h_16 h_2189 True.intro)
    let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i1 _value_i9 h_15 h_2189 True.intro)
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
  have h_2214 : Litex.In _value_i4 (Litex.R (M := M)) := h_17
  have h_2223 : Litex.In _value_i5 (Litex.R (M := M)) := h_18
  exact Litex.HasFiniteFunctionLimit .both _value_i2 _value_i4 _value_i5) :=
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
          have h_2235 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_2234 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2234)
              have h_2234 : Litex.In _value_i3 (Litex.R (M := M)) := h_2234
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          have h_2236 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_2234 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2234)
              have h_2234 : Litex.In _value_i3 (Litex.R (M := M)) := h_2234
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_16
                )
            )
          have h_2237 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_17
                )
            )
          have h_2238 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_18
                )
            )
          have h_2239 : Litex.In _value_i6 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_19
                )
            )
          have h_2240 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i6 h_2239)
                )
            )
          have h_2241 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i6 h_2240)
                )
            )
          have h_2242 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i6 h_2240) _litex_zero.symm)
                )
            )
          have h_4455 : Litex.HasFiniteFunctionLimit .both _value_i2 _value_i4 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_4433 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                          intro _raw_i3 h_2234 _
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2234)
                          have h_2234 : Litex.In _value_i3 (Litex.R (M := M)) := h_2234
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_2234 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2234)
                                  have h_2234 : Litex.In _value_i3 (Litex.R (M := M)) := h_2234
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                              exact h_2235)
                          )
                      )
                    have h_4434 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_4435 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4434
                          )
                      )
                    have h_4436 : Litex.In _value_i4 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2237
                          )
                      )
                    have h_4439 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                          intro _raw_i3 h_2234 _
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2234)
                          have h_2234 : Litex.In _value_i3 (Litex.R (M := M)) := h_2234
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_2234 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2234)
                                  have h_2234 : Litex.In _value_i3 (Litex.R (M := M)) := h_2234
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                              exact h_2236)
                          )
                      )
                    have h_4440 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4434
                          )
                      )
                    have h_4441 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4434
                          )
                      )
                    have h_4442 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i4 _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_4443 : Litex.In _value_i6 (Litex.RPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2239
                          )
                      )
                    have h_4528 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i6 h_4443)
                          )
                      )
                    have h_4529 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i6 h_4528)
                          )
                      )
                    have h_4530 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i6 h_4528) _litex_zero.symm)
                          )
                      )
                    have h_4448 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_4535 : Litex.In _value_i12 (Litex.RPos (M := M))), ∃ (_value_i13 : Litex.Obj (M := M) M.Value), ∃ (h_4539 : Litex.In _value_i13 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i13 _value_i4 (M.real_subset_complex _ h_4539) (M.real_subset_complex _ h_4436));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.subInR _value_i13 _value_i4 h_4539 h_4436))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i13 _value_i4 (M.real_subset_complex _ h_4539) (M.real_subset_complex _ h_4436));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.subInR _value_i13 _value_i4 h_4539 h_4436)))) _value_i12)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i12 _rep_i12 _value_i12 h_4535
                              have h_4536 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRPos_positive _value_i12 h_4535)
                                    )
                                )
                              have h_4537 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i12 h_4536)
                                    )
                                )
                              have h_4538 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i12 h_4536) _litex_zero.symm)
                                    )
                                )
                              exact (h_6 (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) h_4535)
                            )
                          )
                      )
                    have h_4452 : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_6642 : Litex.In _value_i14 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_2_0 := _wd_1_0
                        exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_2_0 := _wd_1_0
                        exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436)))) _value_i6))))
                      exact Litex.Subset _atomic_wd_1_0 (Litex.R (M := M))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_6642 : Litex.In _value_i14 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_2_0 := _wd_1_0
                                exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_2_0 := _wd_1_0
                                exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436)))) _value_i6))))
                              exact (by
                                let _set := _atomic_wd_1_0
                                exact Litex.setBuilderSubset _set.val.bound _set.val.predicate))
                          )
                      )
                    have h_4454 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_8593 : Litex.In _value_i15 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_6642 : Litex.In _value_i14 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436)))) _value_i6))))), (by
                      have h_8594 : (M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_6642 : Litex.In _value_i14 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436)))) _value_i6)))); (Litex.inSetBuilderObj_iff _value_i15 _litex_builder).mp h_8593)).choose
                            )
                        )
                      exact Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i2 _value_i15 h_4439 h_8594 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i1 _value_i15 h_4433 h_8594 True.intro)
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i15 _rep_i15 _value_i15 h_8593
                              have h_8594 : (M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_6642 : Litex.In _value_i14 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                                      (Litex.abs _wd_1_0 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                                      (Litex.abs _wd_1_0 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436)))) _value_i6)))); (Litex.inSetBuilderObj_iff _value_i15 _litex_builder).mp h_8593)).choose
                                    )
                                )
                              have h_8597 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i15) (Litex.denote _value_i4))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i15) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i6) = M.number (_s : ℂ) ∧ _r < _s))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_6642 : Litex.In _value_i14 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                                      (Litex.abs _wd_1_0 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                                      (Litex.abs _wd_1_0 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436)))) _value_i6)))); (Litex.inSetBuilderObj_iff _value_i15 _litex_builder).mp h_8593)).choose_spec
                                    )
                                )
                              have h_8595 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_6642 : Litex.In _value_i14 (Litex.R (M := M))) => (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436))))) (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) h_8594) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.left h_8597)
                                    )
                                )
                              have h_8596 : Litex.Lt ((fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_6642 : Litex.In _value_i14 (Litex.R (M := M))) => (let _wd_1_0 := (Litex.sub _value_i14 _value_i4 (M.real_subset_complex _ h_6642) (M.real_subset_complex _ h_4436));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i14 _value_i4 h_6642 h_4436))))) (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) h_8594) _value_i6 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.right h_8597)
                                    )
                                )
                              exact (h_11 (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) h_8593)
                            )
                          )
                      )
                    exact (show (by
                    have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
                      let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                        intro _raw_i3 h_2234 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2234)
                        have h_2234 : Litex.In _value_i3 (Litex.R (M := M)) := h_2234
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                      have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                        intro _raw_i3 h_2234 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2234)
                        have h_2234 : Litex.In _value_i3 (Litex.R (M := M)) := h_2234
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                        intro _raw_i3 h_2234 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2234)
                        have h_2234 : Litex.In _value_i3 (Litex.R (M := M)) := h_2234
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_4439)
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_4434
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_4434
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    )
                    have h_8628 : Litex.In _value_i4 (Litex.R (M := M)) := h_4436
                    have h_8635 : Litex.In _value_i5 (Litex.R (M := M)) := h_2238
                    exact Litex.HasFiniteFunctionLimit .both _value_i2 _value_i4 _value_i5) from (by
                    let _law0_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                      intro _raw_i3 h_2234 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2234)
                      have h_2234 : Litex.In _value_i3 (Litex.R (M := M)) := h_2234
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                    have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_4433
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
                      refine ⟨_law0_signature, _law0_member, ?_, h_4435⟩
                      intro x hx
                      exact h_4434 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                    let _law1_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                      intro _raw_i3 h_2234 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2234)
                      have h_2234 : Litex.In _value_i3 (Litex.R (M := M)) := h_2234
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                    have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_4439
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
                      refine ⟨_law1_signature, _law1_member, ?_, h_4441⟩
                      intro x hx
                      exact h_4440 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                    exact Litex.finiteFunctionLimitLocalEqual .both (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i4) (Litex.denote _value_i5) (Litex.denote _law1_domain) _value_i6 h_4443 _law_real_1 _law_domain_1 h_4442 h_4448 (by
                      intro input hinput
                      have _member : M.mem input (Litex.denote _law0_domain) := h_4452 input hinput
                      rw [_law_domain_0] at _member
                      exact _member
                    ) (by
                      intro input hinput
                      exact h_4454 (Litex.semanticObject input (M.member_isSet hinput)) hinput
                    )
                  ))
                  )
                )
            )
          exact h_4455
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_at_x5f_local_x5f_equal_x2f_statement_x2e_lit
