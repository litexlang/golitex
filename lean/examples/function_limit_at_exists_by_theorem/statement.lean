import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_at_x5f_exists_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_5 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
    have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_7 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_8 : Litex.In _value_i4 (Litex.R (M := M))) (h_1 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_5 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
      have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_5 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
      have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_5 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
      have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_6)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_11 : Litex.In _value_i3 (Litex.R (M := M)) := h_7
  have h_18 : Litex.In _value_i4 (Litex.R (M := M)) := h_8
  exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i4)), ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_27 : Litex.In _value_i5 (Litex.R (M := M))), Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i5 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i3 _rep_i3 _value_i3 h_7 _Host_i4 _rep_i4 _value_i4 h_8 h_1
          have h_48 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_47 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
              have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_49 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_50 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_77 : ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_137 : Litex.In _value_i6 (Litex.R (M := M))), Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_71 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_47 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                          have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_47 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                                  have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                              exact h_48)
                          )
                      )
                    have h_72 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_73 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_72
                          )
                      )
                    have h_74 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_49
                          )
                      )
                    have h_75 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    exact (show ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_106 : Litex.In _value_i6 (Litex.R (M := M))), Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i6 from Litex.finiteFunctionLimitExists .both _value_i1 _value_i3 _value_i4 h_75)
                  )
                )
            )
          exact h_77
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_at_x5f_exists_x5f_by_x5f_theorem_x2f_statement_x2e_lit
