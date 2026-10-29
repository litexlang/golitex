import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_neg_x5f_inf_x5f_unique_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_6 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
    have h_6 : Litex.In _value_i2 (Litex.R (M := M)) := h_6
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_8 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_9 : Litex.In _value_i4 (Litex.R (M := M))) (h_1 : (by
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
  have h_12 : Litex.In _value_i3 (Litex.R (M := M)) := h_8
  exact Litex.HasInfiniteFunctionLimit .negative _value_i1 _value_i3)) (h_2 : (by
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
  have h_23 : Litex.In _value_i4 (Litex.R (M := M)) := h_9
  exact Litex.HasInfiniteFunctionLimit .negative _value_i1 _value_i4)), Litex.Same _value_i3 _value_i4 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 _Host_i3 _rep_i3 _value_i3 h_8 _Host_i4 _rep_i4 _value_i4 h_9 h_1 h_2
          have h_33 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_32 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_32)
              have h_32 : Litex.In _value_i2 (Litex.R (M := M)) := h_32
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_34 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_35 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_5 : Litex.Same _value_i3 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_60 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_32 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_32)
                          have h_32 : Litex.In _value_i2 (Litex.R (M := M)) := h_32
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_32 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_32)
                                  have h_32 : Litex.In _value_i2 (Litex.R (M := M)) := h_32
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                              exact h_33)
                          )
                      )
                    have h_61 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_62 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_61
                          )
                      )
                    have h_63 : Litex.HasInfiniteFunctionLimit .negative _value_i1 _value_i3 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_64 : Litex.HasInfiniteFunctionLimit .negative _value_i1 _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    have h_65 : Litex.Same _value_i3 _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show Litex.Same _value_i3 _value_i4 from Litex.infiniteFunctionLimitCandidatesEqual .negative _value_i1 _value_i3 _value_i4 h_63 h_64)
                          )
                      )
                    exact (Eq.trans (Eq.symm (Litex.sameRefl _value_i3)) (Eq.trans h_65 (Litex.sameRefl _value_i4)))
                  )
                )
            )
          exact h_5
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_neg_x5f_inf_x5f_unique_x5f_by_x5f_theorem_x2f_statement_x2e_lit
