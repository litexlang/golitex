import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_exists_x5f_object_x2f_statement_x2e_lit

universe u v1 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_6 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
    have h_6 : Litex.In _value_i2 (Litex.R (M := M)) := h_6
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_8 : Litex.In _value_i3 (Litex.R (M := M))) (h_2 : ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_9 : Litex.In _value_i4 (Litex.R (M := M))), Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i4), Litex.IsSet (let _function := _value_i1; let _point := _value_i3; Litex.finiteFunctionLimit .both _function _point (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
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
) h_8 (Litex.finiteFunctionConvergentOfExistence .both _function _point (show ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_37 : Litex.In _value_i5 (Litex.R (M := M))), Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i5 from h_2))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 _Host_i3 _rep_i3 _value_i3 h_8 h_2
          have h_55 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_54 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_54)
              have h_54 : Litex.In _value_i2 (Litex.R (M := M)) := h_54
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_56 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          let _object_w7 := (let _function := _value_i1; let _point := _value_i3; Litex.finiteFunctionLimit .both _function _point (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
            let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_54 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_54)
              have h_54 : Litex.In _value_i2 (Litex.R (M := M)) := h_54
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
            have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_54 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_54)
              have h_54 : Litex.In _value_i2 (Litex.R (M := M)) := h_54
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_54 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_54)
              have h_54 : Litex.In _value_i2 (Litex.R (M := M)) := h_54
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_55)
            have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
            have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
            refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
            intro x hx
            exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          ) h_56 (Litex.finiteFunctionConvergentOfExistence .both _function _point (show ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_85 : Litex.In _value_i6 (Litex.R (M := M))), Litex.HasFiniteFunctionLimit .both _value_i1 _value_i3 _value_i6 from h_2)))

          have h_5 : (by
            let _atomic_wd_1_0 := _object_w7
            exact Litex.IsSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w7
                    exact (Litex.isSet _atomic_wd_1_0))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w7
            exact h_5)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_exists_x5f_object_x2f_statement_x2e_lit
