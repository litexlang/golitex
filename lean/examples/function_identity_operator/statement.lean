import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_identity_x5f_operator_x2f_statement_x2e_lit

universe u v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_22 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_22)
    have h_22 : Litex.In _value_i4 (Litex.R (M := M)) := h_22
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_1 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1)
    have h_1 : Litex.In _value_i2 (Litex.R (M := M)) := h_1
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) (Litex.denote _litex_output) (Litex.isSet (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_1 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1)
    have h_1 : Litex.In _value_i2 (Litex.R (M := M)) := h_1
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => _raw_i3) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_1 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1)
    have h_1 : Litex.In _value_i2 (Litex.R (M := M)) := h_1
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => _raw_i3) _raw_i3) (Litex.denote (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_22 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_22)
    have h_22 : Litex.In _value_i4 (Litex.R (M := M)) := h_22
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) := (by
    intro _raw_i3 h_21 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_21)
    have h_21 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
        intro _raw_i2 h_1 _
        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1)
        have h_1 : Litex.In _value_i2 (Litex.R (M := M)) := h_1
        exact True.intro);
      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) := h_21
    change (by
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_24 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_24)
          have h_24 : Litex.In _value_i4 (Litex.R (M := M)) := h_24
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
      exact Litex.In _value_i3 _atomic_wd_1_1)
    exact (by
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
          intro _raw_i4 h_24 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_24)
          have h_24 : Litex.In _value_i4 (Litex.R (M := M)) := h_24
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
      exact (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
          intro _raw_i2 h_1 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1)
          have h_1 : Litex.In _value_i2 (Litex.R (M := M)) := h_1
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
          intro _raw_i2 h_1 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1)
          have h_1 : Litex.In _value_i2 (Litex.R (M := M)) := h_1
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
        exact (show Litex.Same _left _right from rfl)) h_21)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_1 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1)
    have h_1 : Litex.In _value_i2 (Litex.R (M := M)) := h_1
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) (Litex.denote (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_22 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_22)
    have h_22 : Litex.In _value_i4 (Litex.R (M := M)) := h_22
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) (Litex.isSet (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_1 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1)
    have h_1 : Litex.In _value_i2 (Litex.R (M := M)) := h_1
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) (Litex.isSet (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_22 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_22)
    have h_22 : Litex.In _value_i4 (Litex.R (M := M)) := h_22
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_32 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_33 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_35 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_55 : Litex.In _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
    intro _raw_i6 h_54 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_54)
    have h_54 : Litex.In _value_i6 (Litex.R (M := M)) := h_54
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)))), (by
  let _object_w29 := (let _litex_call_arg_0 := _value_i5;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_32 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
        intro _raw_i2 h_57 _
        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
        have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
        exact True.intro);
      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
    exact (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
        intro _raw_i6 h_54 _
        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_54)
        have h_54 : Litex.In _value_i6 (Litex.R (M := M)) := h_54
        exact True.intro);
      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
        intro _raw_i6 h_54 _
        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_54)
        have h_54 : Litex.In _value_i6 (Litex.R (M := M)) := h_54
        exact True.intro);
      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)))
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_55)), True.intro⟩))
  exact (by
    let _equal_wd_1_0 := _object_w29
    exact Litex.Same _equal_wd_1_0 _value_i5)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_55
          let _object_w29 := (let _litex_call_arg_0 := _value_i5;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_32 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                intro _raw_i2 h_57 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_57)
                have h_57 : Litex.In _value_i2 (Litex.R (M := M)) := h_57
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
            exact (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                intro _raw_i6 h_54 _
                let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_54)
                have h_54 : Litex.In _value_i6 (Litex.R (M := M)) := h_54
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                intro _raw_i6 h_54 _
                let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_54)
                have h_54 : Litex.In _value_i6 (Litex.R (M := M)) := h_54
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)))
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_55)), True.intro⟩))
          have h_34 : (by
            let _equal_wd_1_0 := _object_w29
            exact Litex.Same _equal_wd_1_0 _value_i5) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w29;
                  (show Litex.Same _equal_wd_1_0 _value_i5 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = (Litex.denote _value_i5) from by
                    have _litex_residual : (Litex.denote _value_i5) = (Litex.denote _value_i5) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = (Litex.denote _value_i5) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i5;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_91 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_91)
                      have h_91 : Litex.In _value_i2 (Litex.R (M := M)) := h_91
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_31 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_31)
                      have h_31 : Litex.In _value_i4 (Litex.R (M := M)) := h_31
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_91 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_91)
                        have h_91 : Litex.In _value_i2 (Litex.R (M := M)) := h_91
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                    exact (Litex.inOfSame _wd_1_1 _wd_1_1 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                        intro _raw_i6 h_54 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_54)
                        have h_54 : Litex.In _value_i6 (Litex.R (M := M)) := h_54
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                        intro _raw_i6 h_54 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_54)
                        have h_54 : Litex.In _value_i6 (Litex.R (M := M)) := h_54
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)))
                      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) h_55)) True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => _raw_i3) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i5); exact rfl))
                  ))).trans _litex_residual)))
                )
            )
          exact h_34
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_identity_x5f_operator_x2f_statement_x2e_lit
