import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_function_x5f_membership_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _positive_i2
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_14, _positive_i2⟩)
  have h_15 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i2 h_14)
        )
    )
  have h_16 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_15)
        )
    )
  have h_17 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_15) _litex_zero.symm)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.positiveRealToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.positiveRealToComplex _value_i2 h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.inRPos_real _value_i2 h_14) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_75 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_76 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_78 : Litex.In (_object_i1 (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i3) → True := (by
    intro _raw_i3 h_317 h_77
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_317)
    have h_317 : Litex.In _value_i3 (Litex.R (M := M)) := h_317
    have h_77 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)
              exact h_77)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _membership_function := (_object_i1 (M := M))
          let _membership_target := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i3) → True := (by
              intro _raw_i3 h_81 h_77
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_81)
              have h_81 : Litex.In _value_i3 (Litex.R (M := M)) := h_81
              have h_77 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)
                        exact h_77)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s))))
          have h_94 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_107 : Litex.In _value_i4 (Litex.RPos (M := M))), ((Litex.In _value_i4 (Litex.R (M := M))) ∧ (Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4)) := (by
            intro _Host_i4 _rep_i4 _value_i4 h_107
            have h_108 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_positive _value_i4 h_107)
                  )
              )
            have h_109 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i4 h_108)
                  )
              )
            have h_110 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i4 h_108) _litex_zero.symm)
                  )
              )
            have h_92 : Litex.In _value_i4 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_real _value_i4 h_107)
                  )
              )
            have h_93 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
              (by
                litex_checked_step =>
                  exact (
                    h_108
                  )
              )
            exact (And.intro h_92 h_93)
          )
          have h_150 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_163 : Litex.In _value_i5 (Litex.R (M := M))) (h_148 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5), Litex.In _value_i5 (Litex.RPos (M := M)) := (by
            intro _Host_i5 _rep_i5 _value_i5 h_163 h_148
            have h_149 : Litex.In _value_i5 (Litex.RPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_intro _value_i5 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_148; exact (M.real_members (Litex.denote _value_i5)).mpr ⟨_litex_real, _litex_value⟩) h_148)
                  )
              )
            have h_198 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_positive _value_i5 h_149)
                  )
              )
            have h_199 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i5 h_198)
                  )
              )
            have h_200 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i5 h_198) _litex_zero.symm)
                  )
              )
            exact h_149
          )
          have h_79 : ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_213 : Litex.In _value_i3 (Litex.R (M := M))) (h_77 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3), (by
            let _object_w17 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (_object_i1 (M := M)) _value_i3 (h_75 (M := M)) (Litex.inRPos_real _value_i3 (Litex.inRPos_intro _value_i3 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_77; exact (M.real_members (Litex.denote _value_i3)).mpr ⟨_litex_real, _litex_value⟩) h_77)) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i3)).mp (Litex.inRPos_intro _value_i3 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_77; exact (M.real_members (Litex.denote _value_i3)).mpr ⟨_litex_real, _litex_value⟩) h_77)).2)
            exact (by
              let _atomic_wd_1_0 := _object_w17
              exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i3 _rep_i3 _value_i3 h_213 h_77
                    let _object_w17 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (_object_i1 (M := M)) _value_i3 (h_75 (M := M)) (Litex.inRPos_real _value_i3 (Litex.inRPos_intro _value_i3 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_77; exact (M.real_members (Litex.denote _value_i3)).mpr ⟨_litex_real, _litex_value⟩) h_77)) ((Litex.positiveReal_members (M := M) (Litex.denote _value_i3)).mp (Litex.inRPos_intro _value_i3 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_77; exact (M.real_members (Litex.denote _value_i3)).mpr ⟨_litex_real, _litex_value⟩) h_77)).2)
                    have h_80 : (by
                      let _atomic_wd_1_0 := _object_w17
                      exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := _object_w17
                              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))
                          )
                      )
                    exact h_80
                  )
                )
            )
          exact (by
          let _source_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))
          have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((h_76 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
          have _same_domain : _source_signature.domain = _membership_target.val.domain := (Litex.SetSemantics.ext ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))).domain_isSet ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)))).domain_isSet (fun x => ⟨fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)))).domain from by
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) _litex_input) _).mp _preimage_domain
          have _preimage_positive_i2 := _preimage_guard
          have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.RPos (M := M))) := ((Litex.positiveReal_members (M := M) _preimage_input).mpr ⟨_preimage_members, _preimage_positive_i2⟩)
          have _domain_target := h_94 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base
          have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
          exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(And.left _domain_target), (And.right _domain_target)⟩)
        ) x hx, fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))).domain from by
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.C (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) _litex_input) _).mp _preimage_domain
          have _preimage_guard_0 := _preimage_guard
          have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
          have _domain_target := h_150 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0
          have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
          exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(Litex.inRPos_real (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _domain_target), ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mp _domain_target).2⟩)
        ) x hx⟩))
          change M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _membership_target.val.domain _membership_target.val.output)
          have _source_graph : M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _source_signature.domain _source_signature.output) := _source_member
          rw [_same_domain] at _source_graph
          apply Litex.FunctionSemantics.fnSet_of_returns _source_graph
          intro _input _hin
          change M.mem _input (Litex.SetSemantics.sepValue _ _) at _hin
          obtain ⟨_members, _guard⟩ := (Litex.SetSemantics.sep_members _ _ _).mp _hin
          let _raw_0 := _input
          have _member_0 := _members
          let _arg_0 := Litex.semanticObject (M := M) _raw_0 (M.member_isSet _member_0)
          exact h_79 _arg_0 _member_0 _guard)
        )
      )
  )

noncomputable def _object_i6 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i7 : M.Value) => (M.addValue _raw_i7 (M.number (1 : ℂ)))) (by
  intro _raw_i7 h_389 h_330
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_389)
  have h_389 : Litex.In _value_i7 (Litex.R (M := M)) := h_389
  have h_330 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_330)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_389) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_389) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i7 (Litex.number (M := M) (1 : ℂ)) h_389 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_482 : Litex.In (_object_i6 (M := M)) (Litex.fnSet ((_object_i6 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i6 (M := M)))
      )
  )
theorem h_483 : Litex.Same (_object_i6 (M := M)) (_object_i6 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i6 (M := M)))
      )
  )

theorem h_484 : Litex.In (_object_i6 (M := M)) (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) _raw_i9) → True := (by
    intro _raw_i9 h_813 _positive_i9
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_813)
    have h_813 : Litex.In _value_i9 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i9).mpr ⟨h_813, _positive_i9⟩)
    have h_814 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i9 h_813)
          )
      )
    have h_815 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_814)
          )
      )
    have h_816 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_814) _litex_zero.symm)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _membership_function := (_object_i6 (M := M))
          let _membership_target := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) _raw_i9) → True := (by
              intro _raw_i9 h_487 _positive_i9
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_487)
              have h_487 : Litex.In _value_i9 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i9).mpr ⟨h_487, _positive_i9⟩)
              have h_488 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inRPos_positive _value_i9 h_487)
                    )
                )
              have h_489 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_488)
                    )
                )
              have h_490 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_488) _litex_zero.symm)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9))))
          have h_493 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_506 : Litex.In _value_i10 (Litex.R (M := M))) (h_491 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i10), Litex.In _value_i10 (Litex.RPos (M := M)) := (by
            intro _Host_i10 _rep_i10 _value_i10 h_506 h_491
            have h_492 : Litex.In _value_i10 (Litex.RPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_intro _value_i10 (by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := h_491; exact (M.real_members (Litex.denote _value_i10)).mpr ⟨_litex_real, _litex_value⟩) h_491)
                  )
              )
            have h_557 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_positive _value_i10 h_492)
                  )
              )
            have h_558 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i10 h_557)
                  )
              )
            have h_559 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i10 h_557) _litex_zero.symm)
                  )
              )
            exact h_492
          )
          have h_562 : ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_575 : Litex.In _value_i11 (Litex.RPos (M := M))), ((Litex.In _value_i11 (Litex.R (M := M))) ∧ (Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i11)) := (by
            intro _Host_i11 _rep_i11 _value_i11 h_575
            have h_576 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i11 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_positive _value_i11 h_575)
                  )
              )
            have h_577 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i11 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i11 h_576)
                  )
              )
            have h_578 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i11 h_576) _litex_zero.symm)
                  )
              )
            have h_560 : Litex.In _value_i11 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_real _value_i11 h_575)
                  )
              )
            have h_561 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i11 :=
              (by
                litex_checked_step =>
                  exact (
                    h_576
                  )
              )
            exact (And.intro h_560 h_561)
          )
          have h_485 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_640 : Litex.In _value_i9 (Litex.RPos (M := M))), (by
            have h_641 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_positive _value_i9 h_640)
                  )
              )
            let _object_w41 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i6 (M := M)) _value_i9 (h_482 (M := M)) (Litex.inRPos_real _value_i9 h_640) h_641)
            exact (by
              let _atomic_wd_1_0 := _object_w41
              exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i9 _rep_i9 _value_i9 h_640
                    have h_641 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i9 h_640)
                          )
                      )
                    have h_642 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_641)
                          )
                      )
                    have h_643 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_641) _litex_zero.symm)
                          )
                      )
                    let _object_w41 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i6 (M := M)) _value_i9 (h_482 (M := M)) (Litex.inRPos_real _value_i9 h_640) h_641)
                    have h_486 : (by
                      let _atomic_wd_1_0 := _object_w41
                      exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := _object_w41
                              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))
                          )
                      )
                    exact h_486
                  )
                )
            )
          exact (by
          let _source_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))
          have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame (_object_i6 (M := M)) (_object_i6 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_483 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i6 (M := M))))
          have _same_domain : _source_signature.domain = _membership_target.val.domain := (Litex.SetSemantics.ext ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))).domain_isSet ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)))).domain_isSet (fun x => ⟨fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)))).domain from by
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) _litex_input) _).mp _preimage_domain
          have _preimage_guard_0 := _preimage_guard
          have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
          have _domain_target := h_493 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0
          have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
          exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(Litex.inRPos_real (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _domain_target), ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mp _domain_target).2⟩)
        ) x hx, fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))).domain from by
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.C (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) _litex_input) _).mp _preimage_domain
          have _preimage_positive_i9 := _preimage_guard
          have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.RPos (M := M))) := ((Litex.positiveReal_members (M := M) _preimage_input).mpr ⟨_preimage_members, _preimage_positive_i9⟩)
          have _domain_target := h_562 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base
          have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
          exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i7 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(And.left _domain_target), (And.right _domain_target)⟩)
        ) x hx⟩))
          change M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _membership_target.val.domain _membership_target.val.output)
          have _source_graph : M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _source_signature.domain _source_signature.output) := _source_member
          rw [_same_domain] at _source_graph
          apply Litex.FunctionSemantics.fnSet_of_returns _source_graph
          intro _input _hin
          change M.mem _input (Litex.SetSemantics.sepValue _ _) at _hin
          obtain ⟨_members, _guard⟩ := (Litex.SetSemantics.sep_members _ _ _).mp _hin
          let _raw_0 := _input
          have _member_0 := _members
          let _arg_0 := Litex.semanticObject (M := M) _raw_0 (M.member_isSet _member_0)
          exact h_485 _arg_0 ((Litex.positiveReal_members (M := M) _raw_0).mpr ⟨_member_0, _guard⟩))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_function_x5f_membership_x2f_statement_x2e_lit
