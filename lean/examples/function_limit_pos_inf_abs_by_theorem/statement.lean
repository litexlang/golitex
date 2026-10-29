import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_pos_x5f_inf_x5f_abs_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2 v4 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_7 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7)
    have h_7 : Litex.In _value_i3 (Litex.R (M := M)) := h_7
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_7 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7)
    have h_7 : Litex.In _value_i3 (Litex.R (M := M)) := h_7
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_10 : Litex.In _value_i4 (Litex.R (M := M))) (h_1 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_7 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i3 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_7 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i3 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_7 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i3 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_8)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_13 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
  exact Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i4)) (h_3 : ∀ (_value_i5 : Litex.Obj (M := M) M.Value) (h_22 : Litex.In _value_i5 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i2 _value_i5 h_9 h_22 True.intro)
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i1 _value_i5 h_8 h_22 True.intro);
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), (by
  let _atomic_wd_1_1 := (Litex.abs _value_i4 h_10)
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_7 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i3 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_7 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i3 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_7 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i3 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_9)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_138 : (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (by
      let _litex_abs := _atomic_wd_2_0
      exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
    ))
  exact Litex.HasInfiniteFunctionLimit .positive _value_i2 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8 _Host_i2 _rep_i2 _value_i2 h_9 _Host_i4 _rep_i4 _value_i4 h_10 h_1 h_3
          have h_162 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_161 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_161)
              have h_161 : Litex.In _value_i3 (Litex.R (M := M)) := h_161
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_163 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_161 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_161)
              have h_161 : Litex.In _value_i3 (Litex.R (M := M)) := h_161
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_164 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_6 : (by
            let _atomic_wd_1_1 := (Litex.abs _value_i4 h_164)
            exact Litex.HasInfiniteFunctionLimit .positive _value_i2 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_282 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                          intro _raw_i3 h_161 _
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_161)
                          have h_161 : Litex.In _value_i3 (Litex.R (M := M)) := h_161
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_161 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_161)
                                  have h_161 : Litex.In _value_i3 (Litex.R (M := M)) := h_161
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                              exact h_162)
                          )
                      )
                    have h_283 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_284 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_283
                          )
                      )
                    have h_287 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                          intro _raw_i3 h_161 _
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_161)
                          have h_161 : Litex.In _value_i3 (Litex.R (M := M)) := h_161
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_161 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_161)
                                  have h_161 : Litex.In _value_i3 (Litex.R (M := M)) := h_161
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                              exact h_163)
                          )
                      )
                    have h_288 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_283
                          )
                      )
                    have h_289 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_283
                          )
                      )
                    have h_290 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_291 : Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_293 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_341 : Litex.In _value_i7 (Litex.R (M := M))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i2 _value_i7 h_287 h_341 True.intro) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i1 _value_i7 h_282 h_341 True.intro);
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_return_call := _atomic_wd_1_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i7 _rep_i7 _value_i7 h_341
                              exact (h_3 (Litex.semanticObject (Litex.denote _value_i7) (Litex.isSet _value_i7)) h_341)
                            )
                          )
                      )
                    have h_294 : Litex.HasInfiniteFunctionLimit .positive _value_i2 (Litex.abs _value_i4 h_164) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              let _atomic_wd_1_1 := (Litex.abs _value_i4 h_164)
                              have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
                                let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_161 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_161)
                                  have h_161 : Litex.In _value_i3 (Litex.R (M := M)) := h_161
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                                have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_161 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_161)
                                  have h_161 : Litex.In _value_i3 (Litex.R (M := M)) := h_161
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_161 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_161)
                                  have h_161 : Litex.In _value_i3 (Litex.R (M := M)) := h_161
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_287)
                                have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_283
                                have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_283
                                refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                                intro x hx
                                exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              )
                              have h_571 : (by
                                let _atomic_wd_2_0 := _atomic_wd_1_1
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
                                let _atomic_wd_2_0 := _atomic_wd_1_1
                                exact (by
                                  let _litex_abs := _atomic_wd_2_0
                                  exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
                                ))
                              exact Litex.HasInfiniteFunctionLimit .positive _value_i2 _atomic_wd_1_1) from (by
                              let _law0_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_161 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_161)
                                have h_161 : Litex.In _value_i3 (Litex.R (M := M)) := h_161
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                              have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_282
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
                                refine ⟨_law0_signature, _law0_member, ?_, h_284⟩
                                intro x hx
                                exact h_283 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                              let _law1_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_161 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_161)
                                have h_161 : Litex.In _value_i3 (Litex.R (M := M)) := h_161
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                              have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_287
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
                                refine ⟨_law1_signature, _law1_member, ?_, h_289⟩
                                intro x hx
                                exact h_288 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                              exact Litex.infiniteFunctionLimitMap .positive (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i4) (Litex.denote (Litex.abs _value_i4 h_164)) _law_real_0 _law_real_1 (_law_domain_1.symm.trans (h_290.trans _law_domain_0)) (Litex.absValue (M := M)) (fun x : ℝ => |x|) Litex.absValue_number rfl (by
                                intro input hinput
                                have _law_input : M.mem input (Litex.denote _law0_domain) := by
                                  rw [_law_domain_0]
                                  exact hinput
                                exact h_293 (Litex.semanticObject input (M.member_isSet _law_input)) _law_input
                              ) continuous_abs h_291
                            ))
                          )
                      )
                    exact (by
                    let _atomic_wd_1_1 := (Litex.abs _value_i4 h_164)
                    exact h_294)
                  )
                )
            )
          exact (by
            let _atomic_wd_1_1 := (Litex.abs _value_i4 h_164)
            exact h_6)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_pos_x5f_inf_x5f_abs_x5f_by_x5f_theorem_x2f_statement_x2e_lit
