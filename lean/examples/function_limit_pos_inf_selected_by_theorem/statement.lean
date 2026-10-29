import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_pos_x5f_inf_x5f_selected_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_5 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
    have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) (h_2 : ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_7 : Litex.In _value_i3 (Litex.R (M := M))), Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i3), Litex.HasInfiniteFunctionLimit .positive _value_i1 (let _function := _value_i1; Litex.infiniteFunctionLimit .positive _function (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
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
) (Litex.infiniteFunctionConvergentOfExistence .positive _function (show ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_19 : Litex.In _value_i4 (Litex.R (M := M))), Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i4 from h_2))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 h_2
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
          have h_64 : Litex.HasInfiniteFunctionLimit .positive _value_i1 (let _function := _value_i1; Litex.infiniteFunctionLimit .positive _function (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
            let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_47 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
              have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
            have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_47 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
              have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_47 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
              have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_48)
            have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
            have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
            refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
            intro x hx
            exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          ) (Litex.infiniteFunctionConvergentOfExistence .positive _function (show ∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_183 : Litex.In _value_i11 (Litex.R (M := M))), Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i11 from h_2))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_59 : (by
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
                    have h_60 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_61 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_60
                          )
                      )
                    have h_63 : ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_79 : Litex.In _value_i6 (Litex.R (M := M))), Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    exact (show (by
                    let _atomic_wd_1_1 := (let _function := _value_i1; Litex.infiniteFunctionLimit .positive _function (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                      let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_47 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                        have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                      have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_47 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                        have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_47 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                        have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_59)
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_60
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_60
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    ) (Litex.infiniteFunctionConvergentOfExistence .positive _function (show ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_107 : Litex.In _value_i9 (Litex.R (M := M))), Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i9 from h_63)))
                    have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                      let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_47 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                        have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                      have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_47 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                        have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_47 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                        have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_59)
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_60
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_60
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    )
                    have h_133 : (by
                      let _atomic_wd_2_0 := (let _function := _value_i1; Litex.infiniteFunctionLimit .positive _function (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                        let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_47 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                          have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                        have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_47 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                          have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_47 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                          have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_59)
                        have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_60
                        have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_60
                        refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                        intro x hx
                        exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                      ) (Litex.infiniteFunctionConvergentOfExistence .positive _function (show ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_146 : Litex.In _value_i10 (Litex.R (M := M))), Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i10 from h_63)))
                      exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
                      let _atomic_wd_2_0 := (let _function := _value_i1; Litex.infiniteFunctionLimit .positive _function (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                        let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_47 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                          have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                        have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_47 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                          have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_47 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                          have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_59)
                        have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_60
                        have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_60
                        refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                        intro x hx
                        exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                      ) (Litex.infiniteFunctionConvergentOfExistence .positive _function (show ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_146 : Litex.In _value_i10 (Litex.R (M := M))), Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i10 from h_63)))
                      exact (Litex.infiniteFunctionLimitInR _atomic_wd_2_0))
                    exact Litex.HasInfiniteFunctionLimit .positive _value_i1 _atomic_wd_1_1) from Litex.infiniteFunctionLimitSelected (let _function := _value_i1; Litex.infiniteFunctionLimit .positive _function (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                    let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_47 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                      have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_47 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                      have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_47 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                      have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_59)
                    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_60
                    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_60
                    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                    intro x hx
                    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                  ) (Litex.infiniteFunctionConvergentOfExistence .positive _function (show ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_107 : Litex.In _value_i9 (Litex.R (M := M))), Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i9 from h_63))))
                  )
                )
            )
          exact (by
            let _atomic_wd_1_1 := (let _function := _value_i1; Litex.infiniteFunctionLimit .positive _function (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
              let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                intro _raw_i2 h_47 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
              have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                intro _raw_i2 h_47 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                intro _raw_i2 h_47 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_47)
                have h_47 : Litex.In _value_i2 (Litex.R (M := M)) := h_47
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_48)
              have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
              have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
              refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
              intro x hx
              exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
            ) (Litex.infiniteFunctionConvergentOfExistence .positive _function (show ∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_183 : Litex.In _value_i11 (Litex.R (M := M))), Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i11 from h_2)))
            exact h_64)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_pos_x5f_inf_x5f_selected_x5f_by_x5f_theorem_x2f_statement_x2e_lit
