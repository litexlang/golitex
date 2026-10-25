import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_function_x5f_values_x2f_statement_x2e_lit

universe u v1 v4 v8 v12
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_29 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_27 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_27)
    have h_27 : Litex.In _value_i2 (Litex.R (M := M)) := h_27
    exact True.intro);
  Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_28 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
    have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))), (by
  let _object_w9 := (by
    let _returned_receiver := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_28 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
      have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_29 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
    let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), True.intro⟩)
    exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (2 : ℂ)) _returned_member _returned_domain)
  exact (by
    let _atomic_wd_1_0 := _object_w9
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_29
          let _object_w9 := (by
            let _returned_receiver := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_28 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
              have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_29 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
            let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), True.intro⟩)
            exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (2 : ℂ)) _returned_member _returned_domain)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w9
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))
                )
            )
          exact h_1
        )
      )
  )

theorem h_72 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_113 : Litex.In _value_i4 (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _raw_i5) → True := (by
    intro _raw_i5 h_109 h_69
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_109)
    have h_109 : Litex.In _value_i5 (Litex.R (M := M)) := h_109
    have h_69 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i5 = (M.number (0 : ℂ))))
              exact h_69)
          )
      )
    exact True.intro);
  Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i6 : M.Value) (_raw_i7 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i7 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) _raw_i6 _raw_i7) → True := (by
    intro _raw_i6 _raw_i7 h_110 h_111 h_70
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_110)
    have h_110 : Litex.In _value_i6 (Litex.R (M := M)) := h_110
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_111)
    have h_111 : Litex.In _value_i7 (Litex.R (M := M)) := h_111
    have h_70 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i7 = (M.number (0 : ℂ))))
              exact h_70)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input)))), (by
  let _object_w26 := (by
    let _returned_receiver := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i6 : M.Value) (_raw_i7 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i7 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) _raw_i6 _raw_i7) → True := (by
      intro _raw_i6 _raw_i7 h_110 h_111 h_70
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_110)
      have h_110 : Litex.In _value_i6 (Litex.R (M := M)) := h_110
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_111)
      have h_111 : Litex.In _value_i7 (Litex.R (M := M)) := h_111
      have h_70 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i7 = (M.number (0 : ℂ))))
                exact h_70)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input) _value_i4 _litex_call_arg_0 h_113 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))))
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote (Litex.callArguments2 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)))) _returned_signature.domain := ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (Litex.denote (Litex.number (M := M) (3 : ℂ))) (Litex.denote (Litex.number (M := M) (4 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)), (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)), (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))⟩)
    exact Litex.callOn _returned_signature _returned_receiver (Litex.callArguments2 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ))) _returned_member _returned_domain)
  exact (by
    let _atomic_wd_1_0 := _object_w26
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_113
          let _object_w26 := (by
            let _returned_receiver := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
          Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i6 : M.Value) (_raw_i7 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i7 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) _raw_i6 _raw_i7) → True := (by
              intro _raw_i6 _raw_i7 h_110 h_111 h_70
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_110)
              have h_110 : Litex.In _value_i6 (Litex.R (M := M)) := h_110
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_111)
              have h_111 : Litex.In _value_i7 (Litex.R (M := M)) := h_111
              have h_70 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i7 = (M.number (0 : ℂ))))
                        exact h_70)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input) _value_i4 _litex_call_arg_0 h_113 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))))
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote (Litex.callArguments2 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ)))) _returned_signature.domain := ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (Litex.denote (Litex.number (M := M) (3 : ℂ))) (Litex.denote (Litex.number (M := M) (4 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)), (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)), (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))⟩)
            exact Litex.callOn _returned_signature _returned_receiver (Litex.callArguments2 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (4 : ℂ))) _returned_member _returned_domain)
          have h_71 : (by
            let _atomic_wd_1_0 := _object_w26
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w26
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))
                )
            )
          exact h_71
        )
      )
  )

theorem h_163 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_199 : Litex.In _value_i8 (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
    intro _raw_i9 h_196 _
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_196)
    have h_196 : Litex.In _value_i9 (Litex.R (M := M)) := h_196
    exact True.intro);
  Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
    intro _raw_i10 h_197 _
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_197)
    have h_197 : Litex.In _value_i10 (Litex.R (M := M)) := h_197
    exact True.intro);
  Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → True := (by
    intro _raw_i11 h_198 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_198)
    have h_198 : Litex.In _value_i11 (Litex.R (M := M)) := h_198
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)))), (by
  let _object_w36 := (by
    let _returned_receiver := (by
    let _returned_receiver := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
      intro _raw_i10 h_197 _
      let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_197)
      have h_197 : Litex.In _value_i10 (Litex.R (M := M)) := h_197
      exact True.intro);
    Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → True := (by
      intro _raw_i11 h_198 _
      let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_198)
      have h_198 : Litex.In _value_i11 (Litex.R (M := M)) := h_198
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_199 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
    let _returned_signature : Litex.FunctionSignature M := (let _litex_output := (let _checked_header : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → True := (by
      intro _raw_i11 h_198 _
      let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_198)
      have h_198 : Litex.In _value_i11 (Litex.R (M := M)) := h_198
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input))
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := (let _litex_output := (let _checked_header : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → True := (by
      intro _raw_i11 h_198 _
      let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_198)
      have h_198 : Litex.In _value_i11 (Litex.R (M := M)) := h_198
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True))); (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), True.intro⟩)
    exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (2 : ℂ)) _returned_member _returned_domain)
    let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True))
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (3 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (Litex.denote (Litex.number (M := M) (3 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)), True.intro⟩)
    exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (3 : ℂ)) _returned_member _returned_domain)
  exact (by
    let _atomic_wd_1_0 := _object_w36
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 h_199
          let _object_w36 := (by
            let _returned_receiver := (by
            let _returned_receiver := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
              intro _raw_i10 h_197 _
              let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_197)
              have h_197 : Litex.In _value_i10 (Litex.R (M := M)) := h_197
              exact True.intro);
            Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → True := (by
              intro _raw_i11 h_198 _
              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_198)
              have h_198 : Litex.In _value_i11 (Litex.R (M := M)) := h_198
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_199 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
            let _returned_signature : Litex.FunctionSignature M := (let _litex_output := (let _checked_header : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → True := (by
              intro _raw_i11 h_198 _
              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_198)
              have h_198 : Litex.In _value_i11 (Litex.R (M := M)) := h_198
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input))
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := (let _litex_output := (let _checked_header : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → True := (by
              intro _raw_i11 h_198 _
              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_198)
              have h_198 : Litex.In _value_i11 (Litex.R (M := M)) := h_198
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True))); (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), True.intro⟩)
            exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (2 : ℂ)) _returned_member _returned_domain)
            let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True))
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (3 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => True) (Litex.denote (Litex.number (M := M) (3 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)), True.intro⟩)
            exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (3 : ℂ)) _returned_member _returned_domain)
          have h_162 : (by
            let _atomic_wd_1_0 := _object_w36
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w36
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))
                )
            )
          exact h_162
        )
      )
  )

theorem h_243 : ∀ {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_293 : Litex.In _value_i12 (let _checked_header : ∀ (_raw_i13 : M.Value), M.mem _raw_i13 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i13 : M.Value) => True) _raw_i13) → True := (by
    intro _raw_i13 h_288 _
    let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_288)
    have h_288 : Litex.In _value_i13 (Litex.R (M := M)) := h_288
    exact True.intro);
  Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i14 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i14)) _raw_i14) → True := (by
    intro _raw_i14 h_289 _positive_i14
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_289)
    have h_289 : Litex.In _value_i14 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i14).mpr ⟨h_289, _positive_i14⟩)
    have h_290 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i14 h_289)
          )
      )
    have h_291 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_290)
          )
      )
    have h_292 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_290) _litex_zero.symm)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i14)))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input)))), (by
  let _object_w60 := (by
    let _returned_receiver := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i14 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i14)) _raw_i14) → True := (by
      intro _raw_i14 h_289 _positive_i14
      let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_289)
      have h_289 : Litex.In _value_i14 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i14).mpr ⟨h_289, _positive_i14⟩)
      have h_290 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inRPos_positive _value_i14 h_289)
            )
        )
      have h_291 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_290)
            )
        )
      have h_292 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_290) _litex_zero.symm)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i14)))) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input) _value_i12 _litex_call_arg_0 h_293 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
    let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i14)))
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i14)) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.inRPos_real (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))), ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))).2⟩)
    exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (2 : ℂ)) _returned_member _returned_domain)
  exact (by
    let _atomic_wd_1_0 := _object_w60
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i12 _rep_i12 _value_i12 h_293
          let _object_w60 := (by
            let _returned_receiver := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i14 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i14)) _raw_i14) → True := (by
              intro _raw_i14 h_289 _positive_i14
              let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_289)
              have h_289 : Litex.In _value_i14 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i14).mpr ⟨h_289, _positive_i14⟩)
              have h_290 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inRPos_positive _value_i14 h_289)
                    )
                )
              have h_291 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i14 h_290)
                    )
                )
              have h_292 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i14 h_290) _litex_zero.symm)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i14)))) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input) _value_i12 _litex_call_arg_0 h_293 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
            let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i14)))
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i14 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i14)) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.inRPos_real (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))), ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))).2⟩)
            exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (2 : ℂ)) _returned_member _returned_domain)
          have h_242 : (by
            let _atomic_wd_1_0 := _object_w60
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w60
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))
                )
            )
          exact h_242
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_function_x5f_values_x2f_statement_x2e_lit
