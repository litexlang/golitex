import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_function_x5f_limit_x5f_right_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change Litex.In _value_i2 (Litex.R (M := M))
  exact h_14))
theorem h_21 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_22 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_28 : ∀ (_value_i3 : Litex.Obj (M := M) M.Value) (h_350 : Litex.In _value_i3 (Litex.RPos (M := M))), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_354 : Litex.In _value_i4 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i4 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_354) (Litex.numberInC (M := M) (2 : ℂ)))) ∧ (Litex.Lt (Litex.sub _value_i4 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_354) (Litex.numberInC (M := M) (2 : ℂ))) _value_i3)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_23 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          exact (show ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_31 : Litex.In _value_i3 (Litex.RPos (M := M))), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_35 : Litex.In _value_i4 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i4 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_35) (Litex.numberInC (M := M) (2 : ℂ)))) ∧ (Litex.Lt (Litex.sub _value_i4 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_35) (Litex.numberInC (M := M) (2 : ℂ))) _value_i3)) from (by
          intro _Host _rep _radius _radius_member
          obtain ⟨_input, _input_member, _positive, _near⟩ := Litex.realFiniteLimitAccumulation .right (Litex.number (M := M) (2 : ℂ)) h_23 _radius _radius_member
          exact ⟨_input, _input_member, _positive, _near⟩
        ))
        )
      )
  )

theorem h_604 : Litex.HasFiniteFunctionLimit .right (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_607 : (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                intro _raw_i2 h_20 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20)
                have h_20 : Litex.In _value_i2 (Litex.R (M := M)) := h_20
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
            exact Litex.In (_object_i1 (M := M)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                        intro _raw_i2 h_20 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20)
                        have h_20 : Litex.In _value_i2 (Litex.R (M := M)) := h_20
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                    exact (h_21 (M := M)))
                )
            )
          have h_608 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.subsetRefl (Litex.R (M := M)))
                )
            )
          have h_609 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_608
                )
            )
          have h_610 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_611 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_610
                )
            )
          have h_616 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_648 : Litex.In _value_i5 (Litex.RPos (M := M))), ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_652 : Litex.In _value_i6 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i6 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_652) (Litex.numberInC (M := M) (2 : ℂ)))) ∧ (Litex.Lt (Litex.sub _value_i6 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_652) (Litex.numberInC (M := M) (2 : ℂ))) _value_i5)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i5 _rep_i5 _value_i5 h_648
                    have h_649 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i5 h_648)
                          )
                      )
                    have h_650 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i5 h_649)
                          )
                      )
                    have h_651 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i5 h_649) _litex_zero.symm)
                          )
                      )
                    exact ((h_28 (M := M)) (Litex.semanticObject (Litex.denote _value_i5) (Litex.isSet _value_i5)) h_648)
                  )
                )
            )
          have h_618 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1144 : Litex.In _value_i7 (Litex.R (M := M))), (by
            let _object_w16 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 h_607 h_1144 True.intro)
            exact (by
              let _equal_wd_1_0 := _object_w16
              exact Litex.Same _equal_wd_1_0 _value_i7)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i7 _rep_i7 _value_i7 h_1144
                    let _object_w16 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 h_607 h_1144 True.intro)
                    have h_617 : (by
                      let _equal_wd_1_0 := _object_w16
                      exact Litex.Same _equal_wd_1_0 _value_i7) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (let _equal_wd_1_0 := _object_w16;
                            (show Litex.Same _equal_wd_1_0 _value_i7 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)) = (Litex.denote _value_i7) from by
                              have _litex_residual : (Litex.denote _value_i7) = (Litex.denote _value_i7) := (show @Eq M.Value _ _ from Eq.refl _)
                              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)) = (Litex.denote _value_i7) from by
                              let _litex_original := _equal_wd_1_0
                              let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                              let _wd_1_1 := _value_i7;
                              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_1144 True.intro))
                              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_22 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => _raw_i2) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i7) from rfl))
                            ))).trans _litex_residual)))
                          )
                      )
                    exact h_617
                  )
                )
            )
          have h_619 : Litex.HasFiniteFunctionLimit .right (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (show (by
                    have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) from by
                      let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))
                      have _limit_function : Litex.In (_object_i1 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_22 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_608
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_608
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    )
                    have h_1193 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_610
                    have h_1200 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := h_610
                    exact Litex.HasFiniteFunctionLimit .right (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ))) from (by
                    let _signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))
                    have _member : Litex.In (_object_i1 (M := M)) (Litex.fnSet _signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_22 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
                    let _source_domain := (M.standard Litex.StandardSetValue.real)
                    have _domain_set : M.isSet _source_domain := (Litex.isSet (Litex.R (M := M)))
                    have _domain_match : _source_domain = _signature.domain := by
                      apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
                      intro x
                      change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
                      rw [Litex.SetSemantics.sep_members]
                      exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                    let _domain := Litex.semanticObject _source_domain _domain_set
                    have _constant_real_domain : Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) from by
                    let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))
                    have _limit_function : Litex.In (_object_i1 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_22 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
                    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_608
                    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_608
                    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                    intro x hx
                    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                  )
                    exact Litex.finiteFunctionLimitIdentity .right (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) _domain _constant_real_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_610 h_616 h_618
                  ))
                )
            )
          exact h_619
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_identity_x5f_function_x5f_limit_x5f_right_x5f_by_x5f_theorem_x2f_statement_x2e_lit
