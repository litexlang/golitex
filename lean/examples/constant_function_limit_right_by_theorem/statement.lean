import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_constant_x5f_function_x5f_limit_x5f_right_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v3 v4 v5 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_9 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_12 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_11 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_11)
    have h_11 : Litex.In _value_i2 (Litex.R (M := M)) := h_11
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) (h_5 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_15 : Litex.In _value_i5 (Litex.RPos (M := M))), ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_19 : Litex.In _value_i6 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i6 _value_i3 (M.real_subset_complex _ h_19) (M.real_subset_complex _ h_13))) ∧ (Litex.Lt (Litex.sub _value_i6 _value_i3 (M.real_subset_complex _ h_19) (M.real_subset_complex _ h_13)) _value_i5))) (h_7 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_459 : Litex.In _value_i7 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _value_i7 h_12 h_459 True.intro)
  exact Litex.Same _equal_wd_1_0 _value_i4)), Litex.HasFiniteFunctionLimit .right _value_i1 _value_i3 _value_i4 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_12 _Host_i3 _rep_i3 _value_i3 h_13 _Host_i4 _rep_i4 _value_i4 h_14 h_5 h_7
          have h_484 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_483 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_483)
              have h_483 : Litex.In _value_i2 (Litex.R (M := M)) := h_483
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_485 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          have h_486 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_14
                )
            )
          have h_10 : Litex.HasFiniteFunctionLimit .right _value_i1 _value_i3 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_939 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_483 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_483)
                          have h_483 : Litex.In _value_i2 (Litex.R (M := M)) := h_483
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_483 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_483)
                                  have h_483 : Litex.In _value_i2 (Litex.R (M := M)) := h_483
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                              exact h_484)
                          )
                      )
                    have h_940 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_941 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_940
                          )
                      )
                    have h_942 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_485
                          )
                      )
                    have h_943 : Litex.In _value_i4 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_486
                          )
                      )
                    have h_948 : ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_990 : Litex.In _value_i8 (Litex.RPos (M := M))), ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_994 : Litex.In _value_i9 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i9 _value_i3 (M.real_subset_complex _ h_994) (M.real_subset_complex _ h_942))) ∧ (Litex.Lt (Litex.sub _value_i9 _value_i3 (M.real_subset_complex _ h_994) (M.real_subset_complex _ h_942)) _value_i8)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i8 _rep_i8 _value_i8 h_990
                              have h_991 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.inRPos_positive _value_i8 h_990)
                                    )
                                )
                              have h_992 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i8 h_991)
                                    )
                                )
                              have h_993 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i8 h_991) _litex_zero.symm)
                                    )
                                )
                              exact (h_5 _value_i8 h_990)
                            )
                          )
                      )
                    have h_950 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_1683 : Litex.In _value_i10 (Litex.R (M := M))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _value_i1 _value_i10 h_939 h_1683 True.intro) _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i10 _rep_i10 _value_i10 h_1683
                              exact (h_7 _value_i10 h_1683)
                            )
                          )
                      )
                    have h_951 : Litex.HasFiniteFunctionLimit .right _value_i1 _value_i3 _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
                                let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_483 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_483)
                                  have h_483 : Litex.In _value_i2 (Litex.R (M := M)) := h_483
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                                have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_483 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_483)
                                  have h_483 : Litex.In _value_i2 (Litex.R (M := M)) := h_483
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_483 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_483)
                                  have h_483 : Litex.In _value_i2 (Litex.R (M := M)) := h_483
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_939)
                                have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_940
                                have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_940
                                refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                                intro x hx
                                exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              )
                              have h_1699 : Litex.In _value_i3 (Litex.R (M := M)) := h_942
                              have h_1706 : Litex.In _value_i4 (Litex.R (M := M)) := h_943
                              exact Litex.HasFiniteFunctionLimit .right _value_i1 _value_i3 _value_i4) from (by
                              let _signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_483 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_483)
                                have h_483 : Litex.In _value_i2 (Litex.R (M := M)) := h_483
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                              have _member : Litex.In _value_i1 (Litex.fnSet _signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_483 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_483)
                                have h_483 : Litex.In _value_i2 (Litex.R (M := M)) := h_483
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_483 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_483)
                                have h_483 : Litex.In _value_i2 (Litex.R (M := M)) := h_483
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_939)
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
                                intro _raw_i2 h_483 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_483)
                                have h_483 : Litex.In _value_i2 (Litex.R (M := M)) := h_483
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                              have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_483 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_483)
                                have h_483 : Litex.In _value_i2 (Litex.R (M := M)) := h_483
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                intro _raw_i2 h_483 _
                                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_483)
                                have h_483 : Litex.In _value_i2 (Litex.R (M := M)) := h_483
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_939)
                              have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_940
                              have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_940
                              refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                              intro x hx
                              exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                            )
                              exact Litex.finiteFunctionLimitConstant .right _value_i1 _value_i3 _value_i4 _domain _constant_real_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_942 h_943 h_948 h_950
                            ))
                          )
                      )
                    exact h_951
                  )
                )
            )
          exact h_10
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_constant_x5f_function_x5f_limit_x5f_right_x5f_by_x5f_theorem_x2f_statement_x2e_lit
