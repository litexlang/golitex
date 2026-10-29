import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_equal_x5f_point_x2f_statement_x2e_lit

universe u v1 v3 v4 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_6 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
    have h_6 : Litex.In _value_i2 (Litex.R (M := M)) := h_6
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_8 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_9 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 (Litex.R (M := M))) (h_1 : Litex.Same _value_i3 _value_i4) (h_2 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_6 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
      have h_6 : Litex.In _value_i2 (Litex.R (M := M)) := h_6
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_6 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
      have h_6 : Litex.In _value_i2 (Litex.R (M := M)) := h_6
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_6 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
      have h_6 : Litex.In _value_i2 (Litex.R (M := M)) := h_6
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_7)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_13 : Litex.In _value_i3 (Litex.R (M := M)) := h_8
  have h_20 : Litex.In _value_i5 (Litex.R (M := M)) := h_10
  exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i5)), Litex.HasFiniteFunctionLimit .both _value_i1 _value_i4 _value_i5 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 _Host_i3 _rep_i3 _value_i3 h_8 _Host_i4 _rep_i4 _value_i4 h_9 _Host_i5 _rep_i5 _value_i5 h_10 h_1 h_2
          have h_35 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_34 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_34)
              have h_34 : Litex.In _value_i2 (Litex.R (M := M)) := h_34
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_36 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_37 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_38 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_5 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i4 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote _value_i1) (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote _value_i1) (Litex.denote _value_i3) (Litex.denote _value_i5)) := h_2
                    exact Eq.mp (((((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote _value_i1) (Litex.denote _value_i3) (Litex.denote _value_i5)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) _known_value (Litex.denote _value_i3) (Litex.denote _value_i5))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote _value_i1) _known_value (Litex.denote _value_i5))) h_1))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote _value_i1) (Litex.denote _value_i4) _known_value)) (show @Eq M.Value _ _ from Eq.refl _))) _known_citation
                  )
                )
            )
          exact (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote _value_i1) (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
            have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote _value_i1) (Litex.denote _value_i3) (Litex.denote _value_i5)) := h_2
            exact Eq.mp (((((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote _value_i1) (Litex.denote _value_i3) (Litex.denote _value_i5)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) _known_value (Litex.denote _value_i3) (Litex.denote _value_i5))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote _value_i1) _known_value (Litex.denote _value_i5))) h_1))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) (_known_argument_2 : M.Value) => (Litex.HasFiniteFunctionLimitValue M .both _known_argument_0 _known_argument_1 _known_argument_2)) (Litex.denote _value_i1) (Litex.denote _value_i4) _known_value)) (show @Eq M.Value _ _ from Eq.refl _))) _known_citation
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_equal_x5f_point_x2f_statement_x2e_lit
