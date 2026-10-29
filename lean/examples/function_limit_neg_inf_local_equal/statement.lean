import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_neg_x5f_inf_x5f_local_x5f_equal_x2f_statement_x2e_lit

universe u v1 v2 v4 v5 v6 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_9 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_11 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_10 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_10)
    have h_10 : Litex.In _value_i3 (Litex.R (M := M)) := h_10
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_12 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_10 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_10)
    have h_10 : Litex.In _value_i3 (Litex.R (M := M)) := h_10
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_13 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_14 : Litex.In _value_i5 (Litex.R (M := M))) (h_1 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_10 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i3 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_10 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i3 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_10 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i3 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_11)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_17 : Litex.In _value_i4 (Litex.R (M := M)) := h_13
  exact Litex.HasInfiniteFunctionLimit .negative _value_i1 _value_i4)) (h_4 : ∀ (_value_i6 : Litex.Obj (M := M) M.Value) (h_26 : Litex.In _value_i6 (Litex.R (M := M))), ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_27 : Litex.In _value_i7 (Litex.R (M := M))), Litex.Lt _value_i7 _value_i6) (h_7 : ∀ (_value_i8 : Litex.Obj (M := M) M.Value) (h_95 : Litex.In _value_i8 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_59 : Litex.In _value_i9 (Litex.R (M := M))) => Litex.Lt _value_i9 _value_i5))), (by
  have h_96 : (M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_59 : Litex.In _value_i9 (Litex.R (M := M))) => Litex.Lt _value_i9 _value_i5)); (Litex.inSetBuilderObj_iff _value_i8 _litex_builder).mp h_95)).choose
        )
    )
  exact (by
    let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i2 _value_i8 h_12 h_96 True.intro)
    let _equal_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i1 _value_i8 h_11 h_96 True.intro)
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
)), (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_10 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i3 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_10 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i3 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_10 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i3 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_12)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_119 : Litex.In _value_i4 (Litex.R (M := M)) := h_13
  exact Litex.HasInfiniteFunctionLimit .negative _value_i2 _value_i4) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_11 _Host_i2 _rep_i2 _value_i2 h_12 _Host_i4 _rep_i4 _value_i4 h_13 _Host_i5 _rep_i5 _value_i5 h_14 h_1 h_4 h_7
          have h_129 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_128 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_128)
              have h_128 : Litex.In _value_i3 (Litex.R (M := M)) := h_128
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_130 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_128 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_128)
              have h_128 : Litex.In _value_i3 (Litex.R (M := M)) := h_128
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_131 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          have h_132 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_14
                )
            )
          have h_253 : Litex.HasInfiniteFunctionLimit .negative _value_i2 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_236 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                          intro _raw_i3 h_128 _
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_128)
                          have h_128 : Litex.In _value_i3 (Litex.R (M := M)) := h_128
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_128 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_128)
                                  have h_128 : Litex.In _value_i3 (Litex.R (M := M)) := h_128
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                              exact h_129)
                          )
                      )
                    have h_237 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_238 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_237
                          )
                      )
                    have h_241 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                          intro _raw_i3 h_128 _
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_128)
                          have h_128 : Litex.In _value_i3 (Litex.R (M := M)) := h_128
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_128 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_128)
                                  have h_128 : Litex.In _value_i3 (Litex.R (M := M)) := h_128
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                              exact h_130)
                          )
                      )
                    have h_242 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_237
                          )
                      )
                    have h_243 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_237
                          )
                      )
                    have h_244 : Litex.HasInfiniteFunctionLimit .negative _value_i1 _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_245 : Litex.In _value_i5 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_132
                          )
                      )
                    have h_248 : ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_314 : Litex.In _value_i11 (Litex.R (M := M))), ∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_315 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Lt _value_i12 _value_i11 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i11 _rep_i11 _value_i11 h_314
                              exact (h_4 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) h_314)
                            )
                          )
                      )
                    have h_250 : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_353 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt _value_i13 _value_i5))
                      exact Litex.Subset _atomic_wd_1_0 (Litex.R (M := M))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_353 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt _value_i13 _value_i5))
                              exact (by
                                let _set := _atomic_wd_1_0
                                exact Litex.setBuilderSubset _set.val.bound _set.val.predicate))
                          )
                      )
                    have h_252 : ∀ {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_413 : Litex.In _value_i14 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_353 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt _value_i13 _value_i5))), (by
                      have h_414 : (M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_353 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt _value_i13 _value_i5)); (Litex.inSetBuilderObj_iff _value_i14 _litex_builder).mp h_413)).choose
                            )
                        )
                      exact Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i2 _value_i14 h_241 h_414 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i1 _value_i14 h_236 h_414 True.intro)
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i14 _rep_i14 _value_i14 h_413
                              have h_414 : (M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_353 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt _value_i13 _value_i5)); (Litex.inSetBuilderObj_iff _value_i14 _litex_builder).mp h_413)).choose
                                    )
                                )
                              have h_415 : (∃ (_r _s : ℝ), (Litex.denote _value_i14) = M.number (_r : ℂ) ∧ (Litex.denote _value_i5) = M.number (_s : ℂ) ∧ _r < _s) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_353 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt _value_i13 _value_i5)); (Litex.inSetBuilderObj_iff _value_i14 _litex_builder).mp h_413)).choose_spec
                                    )
                                )
                              exact (h_7 (Litex.semanticObject (Litex.denote _value_i14) (Litex.isSet _value_i14)) h_413)
                            )
                          )
                      )
                    exact (show (by
                    have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
                      let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                        intro _raw_i3 h_128 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_128)
                        have h_128 : Litex.In _value_i3 (Litex.R (M := M)) := h_128
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                      have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                        intro _raw_i3 h_128 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_128)
                        have h_128 : Litex.In _value_i3 (Litex.R (M := M)) := h_128
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                        intro _raw_i3 h_128 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_128)
                        have h_128 : Litex.In _value_i3 (Litex.R (M := M)) := h_128
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_241)
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_237
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_237
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    )
                    have h_446 : Litex.In _value_i4 (Litex.R (M := M)) := h_131
                    exact Litex.HasInfiniteFunctionLimit .negative _value_i2 _value_i4) from (by
                    let _law0_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                      intro _raw_i3 h_128 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_128)
                      have h_128 : Litex.In _value_i3 (Litex.R (M := M)) := h_128
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                    have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_236
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
                      refine ⟨_law0_signature, _law0_member, ?_, h_238⟩
                      intro x hx
                      exact h_237 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                    let _law1_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                      intro _raw_i3 h_128 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_128)
                      have h_128 : Litex.In _value_i3 (Litex.R (M := M)) := h_128
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                    have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_241
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
                      refine ⟨_law1_signature, _law1_member, ?_, h_243⟩
                      intro x hx
                      exact h_242 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                    exact Litex.infiniteFunctionLimitLocalEqual .negative (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i4) (Litex.denote _law1_domain) _value_i5 h_245 _law_real_1 _law_domain_1 h_244 h_248 (by
                      intro input hinput
                      have _member : M.mem input (Litex.denote _law0_domain) := h_250 input hinput
                      rw [_law_domain_0] at _member
                      exact _member
                    ) (by
                      intro input hinput
                      exact h_252 (Litex.semanticObject input (M.member_isSet hinput)) hinput
                    )
                  ))
                  )
                )
            )
          exact h_253
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_neg_x5f_inf_x5f_local_x5f_equal_x2f_statement_x2e_lit
