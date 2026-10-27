import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_function_x5f_membership_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_4 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4)
    have h_4 : Litex.In _value_i2 (Litex.R (M := M)) := h_4
    exact True.intro);
  Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_5 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_5)
    have h_5 : Litex.In _value_i3 (Litex.R (M := M)) := h_5
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))), (by
  let _atomic_wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_5 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_5)
      have h_5 : Litex.In _value_i3 (Litex.R (M := M)) := h_5
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_6 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
  let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_10 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i4 : M.Value) => True)))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6
          have h_14 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_12 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_12)
              have h_12 : Litex.In _value_i2 (Litex.R (M := M)) := h_12
              exact True.intro);
            Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_13 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
              have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_3 : (by
            let _atomic_wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
            Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                intro _raw_i3 h_13 _
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                intro _raw_i6 h_108 _
                let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_108)
                have h_108 : Litex.In _value_i6 (Litex.R (M := M)) := h_108
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True)))
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _membership_function := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
                    Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                        intro _raw_i3 h_13 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                        have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
                    let _membership_target := (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → True := (by
                        intro _raw_i5 h_21 _
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_21)
                        have h_21 : Litex.In _value_i5 (Litex.R (M := M)) := h_21
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => True)))
                    have h_16 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_37 : Litex.In _value_i5 (Litex.R (M := M))), (by
                      let _object_w8 := (by
                        let _returned_receiver := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
                      Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                          intro _raw_i3 h_13 _
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                          have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
                        let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))
                        have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
                        have _returned_domain : M.mem (Litex.denote _value_i5) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (Litex.denote _value_i5)).mpr ⟨h_37, True.intro⟩)
                        exact Litex.callOn _returned_signature _returned_receiver _value_i5 _returned_member _returned_domain)
                      exact (by
                        let _atomic_wd_1_0 := _object_w8
                        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i5 _rep_i5 _value_i5 h_37
                              let _object_w8 := (by
                                let _returned_receiver := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
                              Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_13 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                                  have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
                                let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))
                                have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
                                have _returned_domain : M.mem (Litex.denote _value_i5) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (Litex.denote _value_i5)).mpr ⟨h_37, True.intro⟩)
                                exact Litex.callOn _returned_signature _returned_receiver _value_i5 _returned_member _returned_domain)
                              have h_17 : (by
                                let _atomic_wd_1_0 := _object_w8
                                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _atomic_wd_1_0 := _object_w8
                                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))
                                    )
                                )
                              exact h_17
                            )
                          )
                      )
                    have h_15 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
                    Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                        intro _raw_i3 h_13 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                        have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro) (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → True := (by
                        intro _raw_i5 h_106 _
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_106)
                        have h_106 : Litex.In _value_i5 (Litex.R (M := M)) := h_106
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => True))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _source_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))
                              have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (by
                              let _returned_signature : Litex.FunctionSignature M := (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_13 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                                have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))
                              have _returned_source : Litex.In _value_i1 (Litex.fnSet _returned_signature) := (Litex.inOfSame _value_i1 _value_i1 (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_13 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                                have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_13 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                                have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_13 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                                have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))) h_14)
                              have _returned_input : M.mem (Litex.denote (Litex.number (M := M) (1 : ℂ))) _returned_signature.domain := ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) (Litex.denote (Litex.number (M := M) (1 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), True.intro⟩)
                              have _returned_member : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
                            Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_13 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                                have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_13 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                                have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) := Litex.FunctionSemantics.call_mem _returned_signature.domain _returned_signature.output (Litex.denote _value_i1) (Litex.denote (Litex.number (M := M) (1 : ℂ))) _returned_source _returned_input
                              exact Litex.inOfSame (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
                            Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_13 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                                have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro) (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
                            Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_13 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                                have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_13 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                                have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) _returned_member)
                              have _same_domain : _source_signature.domain = _membership_target.val.domain := (by rfl)
                              change M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _membership_target.val.domain _membership_target.val.output)
                              have _source_graph : M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _source_signature.domain _source_signature.output) := _source_member
                              rw [_same_domain] at _source_graph
                              apply Litex.FunctionSemantics.fnSet_of_returns _source_graph
                              intro _input _hin
                              change M.mem _input (Litex.SetSemantics.sepValue _ _) at _hin
                              obtain ⟨_members, _guard⟩ := (Litex.SetSemantics.sep_members _ _ _).mp _hin
                              let _raw_0 := _input
                              have _member_0 := _members
                              let _arg_0 := Litex.semanticObject (M := M) _raw_0 (M.member_isSet _member_0)
                              exact h_16 _arg_0 _member_0)
                          )
                      )
                    exact (by
                    let _atomic_wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
                    Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                        intro _raw_i3 h_13 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                        have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                        intro _raw_i6 h_108 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_108)
                        have h_108 : Litex.In _value_i6 (Litex.R (M := M)) := h_108
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True)))
                    exact (Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → True := (by
                        intro _raw_i5 h_106 _
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_106)
                        have h_106 : Litex.In _value_i5 (Litex.R (M := M)) := h_106
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => True))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → True := (by
                        intro _raw_i5 h_106 _
                        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_106)
                        have h_106 : Litex.In _value_i5 (Litex.R (M := M)) := h_106
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => True)))
                      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) h_15))
                  )
                )
            )
          exact (by
            let _atomic_wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
            Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                intro _raw_i3 h_13 _
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_13)
                have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_13
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                intro _raw_i4 h_116 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_116)
                have h_116 : Litex.In _value_i4 (Litex.R (M := M)) := h_116
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i4 : M.Value) => True)))
            exact (Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                intro _raw_i6 h_114 _
                let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_114)
                have h_114 : Litex.In _value_i6 (Litex.R (M := M)) := h_114
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                intro _raw_i6 h_114 _
                let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_114)
                have h_114 : Litex.In _value_i6 (Litex.R (M := M)) := h_114
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True)))
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_3))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_function_x5f_membership_x2f_statement_x2e_lit
