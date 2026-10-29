import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_left_x5f_accumulation_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v3 v4 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_7 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
    have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_9 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_10 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_11 : Litex.In _value_i5 (Litex.RPos (M := M))) (h_1 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_7 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_7 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_7 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7)
      have h_7 : Litex.In _value_i2 (Litex.R (M := M)) := h_7
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_8)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_17 : Litex.In _value_i3 (Litex.R (M := M)) := h_9
  have h_24 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
  exact Litex.HasFiniteFunctionLimit .left _value_i1 _value_i3 _value_i4)), ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_33 : Litex.In _value_i6 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i3 _value_i6 (M.real_subset_complex _ h_9) (M.real_subset_complex _ h_33))) ∧ (Litex.Lt (Litex.sub _value_i3 _value_i6 (M.real_subset_complex _ h_9) (M.real_subset_complex _ h_33)) _value_i5)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8 _Host_i3 _rep_i3 _value_i3 h_9 _Host_i4 _rep_i4 _value_i4 h_10 _Host_i5 _rep_i5 _value_i5 h_11 h_1
          have h_12 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i5 h_11)
                )
            )
          have h_13 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i5 h_12)
                )
            )
          have h_14 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i5 h_12) _litex_zero.symm)
                )
            )
          have h_465 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_464 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_464)
              have h_464 : Litex.In _value_i2 (Litex.R (M := M)) := h_464
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_466 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_467 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_468 : Litex.In _value_i5 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_469 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i5 h_468)
                )
            )
          have h_470 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i5 h_469)
                )
            )
          have h_471 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i5 h_469) _litex_zero.symm)
                )
            )
          have h_501 : ∀ (_value_i8 : Litex.Obj (M := M) M.Value) (h_1231 : Litex.In _value_i8 (Litex.RPos (M := M))), ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_1235 : Litex.In _value_i9 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i3 _value_i9 (M.real_subset_complex _ h_466) (M.real_subset_complex _ h_1235))) ∧ (Litex.Lt (Litex.sub _value_i3 _value_i9 (M.real_subset_complex _ h_466) (M.real_subset_complex _ h_1235)) _value_i8)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_492 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_464 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_464)
                          have h_464 : Litex.In _value_i2 (Litex.R (M := M)) := h_464
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_464 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_464)
                                  have h_464 : Litex.In _value_i2 (Litex.R (M := M)) := h_464
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                              exact h_465)
                          )
                      )
                    have h_493 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_494 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_493
                          )
                      )
                    have h_495 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_466
                          )
                      )
                    have h_496 : Litex.HasFiniteFunctionLimit .left _value_i1 _value_i3 _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    exact (show ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_530 : Litex.In _value_i8 (Litex.RPos (M := M))), ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_534 : Litex.In _value_i9 (Litex.R (M := M))), ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i3 _value_i9 (M.real_subset_complex _ h_495) (M.real_subset_complex _ h_534))) ∧ (Litex.Lt (Litex.sub _value_i3 _value_i9 (M.real_subset_complex _ h_495) (M.real_subset_complex _ h_534)) _value_i8)) from (by
                    let _signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_464 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_464)
                      have h_464 : Litex.In _value_i2 (Litex.R (M := M)) := h_464
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                    have _member : Litex.In _value_i1 (Litex.fnSet _signature) := h_492
                    let _source_domain := (M.standard Litex.StandardSetValue.real)
                    have _domain_set : M.isSet _source_domain := (Litex.isSet (Litex.R (M := M)))
                    have _domain_match : _source_domain = _signature.domain := by
                      apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
                      intro x
                      change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
                      rw [Litex.SetSemantics.sep_members]
                      exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                    let _domain := Litex.semanticObject _source_domain _domain_set
                    intro _Host _rep _limit_radius _limit_radius_member
                    obtain ⟨_limit_input, _limit_input_member, _limit_positive, _limit_near⟩ := Litex.finiteFunctionLimitAccumulation .left _value_i1 _value_i3 _value_i4 _domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_496 _limit_radius _limit_radius_member
                    exact ⟨_limit_input, _limit_input_member, _limit_positive, _limit_near⟩
                  ))
                  )
                )
            )
          exact (by
            have h_2188 : Litex.In _value_i5 (Litex.RPos (M := M)) :=
              h_468
            rcases (h_501 (Litex.semanticObject (Litex.denote _value_i5) (Litex.isSet _value_i5)) h_2188) with ⟨_value_i6, h_1742, h_4⟩
            have h_2 :=
              (And.left h_4)
            have h_3 :=
              (And.right h_4)
            have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
            have _exist_match_1 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (0 : ℂ)))
            have _exist_match_2 : Litex.Same (Litex.sub _value_i3 _value_i6 (M.real_subset_complex _ h_466) (M.real_subset_complex _ h_1742)) (Litex.sub _value_i3 _value_i6 (M.real_subset_complex _ h_466) (M.real_subset_complex _ h_1742)) := (Litex.sameRefl (Litex.sub _value_i3 _value_i6 (M.real_subset_complex _ h_466) (M.real_subset_complex _ h_1742)))
            have _exist_match_3 : Litex.Same (Litex.sub _value_i3 _value_i6 (M.real_subset_complex _ h_466) (M.real_subset_complex _ h_1742)) (Litex.sub _value_i3 _value_i6 (M.real_subset_complex _ h_466) (M.real_subset_complex _ h_1742)) := (Litex.sameRefl (Litex.sub _value_i3 _value_i6 (M.real_subset_complex _ h_466) (M.real_subset_complex _ h_1742)))
            have _exist_match_4 : Litex.Same _value_i5 _value_i5 := (Litex.sameRefl _value_i5)
            exact ⟨_value_i6, h_1742, h_4⟩
          )
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_left_x5f_accumulation_x5f_by_x5f_theorem_x2f_statement_x2e_lit
