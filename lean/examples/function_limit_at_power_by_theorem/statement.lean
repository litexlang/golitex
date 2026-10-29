import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_at_x5f_power_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2 v4 v5 v6
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
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_10 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_11 : Litex.In _value_i5 (Litex.R (M := M))) (h_1 : (by
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
  have h_14 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
  have h_23 : Litex.In _value_i5 (Litex.R (M := M)) := h_11
  exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i4 _value_i5)) (h_3 : ∀ (_value_i6 : Litex.Obj (M := M) M.Value) (h_34 : Litex.In _value_i6 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i2 _value_i6 h_9 h_34 True.intro)
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i1 _value_i6 h_8 h_34 True.intro);
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), (by
  let _atomic_wd_1_2 := (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_11 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
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
  have h_190 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
  have h_199 : (by
    let _atomic_wd_2_0 := _atomic_wd_1_2
    exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
    let _atomic_wd_2_0 := _atomic_wd_1_2
    exact (by
      let _litex_power := _atomic_wd_2_0
      have _elaborated_power_base := h_11
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInR _litex_power _recorded_power_base
    ))
  exact Litex.HasFiniteFunctionLimit .both _value_i2 _value_i4 _atomic_wd_1_2) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8 _Host_i2 _rep_i2 _value_i2 h_9 _Host_i4 _rep_i4 _value_i4 h_10 _Host_i5 _rep_i5 _value_i5 h_11 h_1 h_3
          have h_249 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_248 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_248)
              have h_248 : Litex.In _value_i3 (Litex.R (M := M)) := h_248
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_250 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_248 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_248)
              have h_248 : Litex.In _value_i3 (Litex.R (M := M)) := h_248
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_251 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_252 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_6 : (by
            have h_421 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                  )
              )
            exact (by
              let _atomic_wd_1_2 := (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_252 h_421 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
              exact Litex.HasFiniteFunctionLimit .both _value_i2 _value_i4 _atomic_wd_1_2)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_410 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                          intro _raw_i3 h_248 _
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_248)
                          have h_248 : Litex.In _value_i3 (Litex.R (M := M)) := h_248
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_248 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_248)
                                  have h_248 : Litex.In _value_i3 (Litex.R (M := M)) := h_248
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                              exact h_249)
                          )
                      )
                    have h_411 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_412 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_411
                          )
                      )
                    have h_413 : Litex.In _value_i4 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_251
                          )
                      )
                    have h_416 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                          intro _raw_i3 h_248 _
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_248)
                          have h_248 : Litex.In _value_i3 (Litex.R (M := M)) := h_248
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_248 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_248)
                                  have h_248 : Litex.In _value_i3 (Litex.R (M := M)) := h_248
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                              exact h_250)
                          )
                      )
                    have h_417 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_411
                          )
                      )
                    have h_418 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_411
                          )
                      )
                    have h_419 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_420 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i4 _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_421 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                          )
                      )
                    have h_494 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative (Litex.number (M := M) (2 : ℂ)) h_421)
                          )
                      )
                    have h_423 : ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_500 : Litex.In _value_i8 (Litex.R (M := M))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i2 _value_i8 h_416 h_500 True.intro) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i1 _value_i8 h_410 h_500 True.intro);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (by
                        let _litex_return_call := _atomic_wd_1_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) h_421 (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i8 _rep_i8 _value_i8 h_500
                              exact (h_3 (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) h_500)
                            )
                          )
                      )
                    have h_424 : Litex.HasFiniteFunctionLimit .both _value_i2 _value_i4 (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_252 h_421 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              let _atomic_wd_1_2 := (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_252 h_421 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                              have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
                                let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_248 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_248)
                                  have h_248 : Litex.In _value_i3 (Litex.R (M := M)) := h_248
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                                have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_248 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_248)
                                  have h_248 : Litex.In _value_i3 (Litex.R (M := M)) := h_248
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_248 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_248)
                                  have h_248 : Litex.In _value_i3 (Litex.R (M := M)) := h_248
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_416)
                                have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_411
                                have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_411
                                refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                                intro x hx
                                exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              )
                              have h_838 : Litex.In _value_i4 (Litex.R (M := M)) := h_413
                              have h_845 : (by
                                let _atomic_wd_2_0 := _atomic_wd_1_2
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
                                let _atomic_wd_2_0 := _atomic_wd_1_2
                                exact (by
                                  let _litex_power := _atomic_wd_2_0
                                  have _elaborated_power_base := h_252
                                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                                ))
                              exact Litex.HasFiniteFunctionLimit .both _value_i2 _value_i4 _atomic_wd_1_2) from (by
                              let _law0_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_248 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_248)
                                have h_248 : Litex.In _value_i3 (Litex.R (M := M)) := h_248
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                              have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_410
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
                                refine ⟨_law0_signature, _law0_member, ?_, h_412⟩
                                intro x hx
                                exact h_411 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                              let _law1_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_248 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_248)
                                have h_248 : Litex.In _value_i3 (Litex.R (M := M)) := h_248
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                              have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_416
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
                                refine ⟨_law1_signature, _law1_member, ?_, h_418⟩
                                intro x hx
                                exact h_417 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                              let _law_parameter := Litex.NativeBridge.asNat (Litex.number (M := M) (2 : ℂ)) h_421
                              have _law_parameter_value : Litex.denote (Litex.number (M := M) (2 : ℂ)) = M.number (_law_parameter : ℂ) := Litex.NativeBridge.asNat_spec (Litex.number (M := M) (2 : ℂ)) h_421
                              exact Litex.finiteFunctionLimitMap .both (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i4) (Litex.denote _value_i5) (Litex.denote (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_252 h_421 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) _law_real_0 _law_real_1 (_law_domain_1.symm.trans (h_419.trans _law_domain_0)) (fun value => M.powValue value (Litex.denote (Litex.number (M := M) (2 : ℂ)))) (fun x : ℝ => x^_law_parameter) (by intro x; rw [_law_parameter_value, M.pow_numbers_nat, Complex.ofReal_pow]) rfl (by
                                intro input hinput
                                have _law_input : M.mem input (Litex.denote _law0_domain) := by
                                  rw [_law_domain_0]
                                  exact hinput
                                exact h_423 (Litex.semanticObject input (M.member_isSet _law_input)) _law_input
                              ) (continuous_id.pow _law_parameter) h_420
                            ))
                          )
                      )
                    exact (by
                    let _atomic_wd_1_2 := (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_252 h_421 (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                    exact h_424)
                  )
                )
            )
          exact (by
            let _atomic_wd_1_2 := (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_252 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
            exact h_6)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_at_x5f_power_x5f_by_x5f_theorem_x2f_statement_x2e_lit
