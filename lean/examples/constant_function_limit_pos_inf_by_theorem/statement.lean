import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_constant_x5f_function_x5f_limit_x5f_pos_x5f_inf_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v3 v4 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_7 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_10 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_9 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_9)
    have h_9 : Litex.In _value_i2 (Litex.R (M := M)) := h_9
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_11 : Litex.In _value_i3 (Litex.R (M := M))) (h_3 : ∀ (_value_i4 : Litex.Obj (M := M) M.Value) (h_12 : Litex.In _value_i4 (Litex.R (M := M))), ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_13 : Litex.In _value_i5 (Litex.R (M := M))), Litex.Lt _value_i4 _value_i5) (h_5 : ∀ (_value_i6 : Litex.Obj (M := M) M.Value) (h_43 : Litex.In _value_i6 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _value_i6 h_10 h_43 True.intro)
  exact Litex.Same _equal_wd_1_0 _value_i3)), Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i3 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_10 _Host_i3 _rep_i3 _value_i3 h_11 h_3 h_5
          have h_59 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_58 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
              have h_58 : Litex.In _value_i2 (Litex.R (M := M)) := h_58
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_60 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_8 : Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_100 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_58 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
                          have h_58 : Litex.In _value_i2 (Litex.R (M := M)) := h_58
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_58 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
                                  have h_58 : Litex.In _value_i2 (Litex.R (M := M)) := h_58
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                              exact h_59)
                          )
                      )
                    have h_101 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_102 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_101
                          )
                      )
                    have h_103 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_60
                          )
                      )
                    have h_106 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_136 : Litex.In _value_i7 (Litex.R (M := M))), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_137 : Litex.In _value_i8 (Litex.R (M := M))), Litex.Lt _value_i7 _value_i8 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i7 _rep_i7 _value_i7 h_136
                              exact (h_3 (Litex.semanticObject (Litex.denote _value_i7) (Litex.isSet _value_i7)) h_136)
                            )
                          )
                      )
                    have h_108 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_178 : Litex.In _value_i9 (Litex.R (M := M))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _value_i9 h_100 h_178 True.intro) _value_i3 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i9 _rep_i9 _value_i9 h_178
                              exact (h_5 (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) h_178)
                            )
                          )
                      )
                    have h_109 : Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i3 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                                let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_58 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
                                  have h_58 : Litex.In _value_i2 (Litex.R (M := M)) := h_58
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                                have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_58 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
                                  have h_58 : Litex.In _value_i2 (Litex.R (M := M)) := h_58
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_58 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
                                  have h_58 : Litex.In _value_i2 (Litex.R (M := M)) := h_58
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_100)
                                have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_101
                                have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_101
                                refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                                intro x hx
                                exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              )
                              have h_194 : Litex.In _value_i3 (Litex.R (M := M)) := h_103
                              exact Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i3) from (by
                              let _signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_58 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
                                have h_58 : Litex.In _value_i2 (Litex.R (M := M)) := h_58
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                              have _member : Litex.In _value_i1 (Litex.fnSet _signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_58 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
                                have h_58 : Litex.In _value_i2 (Litex.R (M := M)) := h_58
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_58 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
                                have h_58 : Litex.In _value_i2 (Litex.R (M := M)) := h_58
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_100)
                              let _source_domain := (M.standard Litex.StandardSetValue.real)
                              have _domain_set : M.isSet _source_domain := (Litex.isSet (Litex.R (M := M)))
                              have _domain_match : _source_domain = _signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
                                intro x
                                change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
                                rw [Litex.SetSemantics.sep_members]
                                exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                              let _domain := Litex.semanticObject _source_domain _domain_set
                              have _constant_real_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                              let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_58 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
                                have h_58 : Litex.In _value_i2 (Litex.R (M := M)) := h_58
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                              have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_58 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
                                have h_58 : Litex.In _value_i2 (Litex.R (M := M)) := h_58
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_58 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
                                have h_58 : Litex.In _value_i2 (Litex.R (M := M)) := h_58
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_100)
                              have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_101
                              have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_101
                              refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                              intro x hx
                              exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                            )
                              exact Litex.infiniteFunctionLimitConstant .positive _value_i1 _value_i3 _domain _constant_real_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_103 h_106 h_108
                            ))
                          )
                      )
                    exact h_109
                  )
                )
            )
          exact h_8
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_constant_x5f_function_x5f_limit_x5f_pos_x5f_inf_x5f_by_x5f_theorem_x2f_statement_x2e_lit
