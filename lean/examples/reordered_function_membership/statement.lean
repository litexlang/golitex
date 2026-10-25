import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_reordered_x5f_function_x5f_membership_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  rintro _raw_i2 h_71 ⟨h_1, h_2⟩
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_71)
  have h_71 : Litex.In _value_i2 (Litex.R (M := M)) := h_71
  have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i2 = (M.number (0 : ℂ))))
            exact h_1)
        )
    )
  have h_2 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i2 = (M.number (1 : ℂ))))
            exact h_2)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_71) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_71) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i2 (Litex.number (M := M) (1 : ℂ)) h_71 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_114 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_115 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_118 : Litex.In (_object_i1 (M := M)) (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))) _raw_i5) → True := (by
    rintro _raw_i5 h_292 ⟨h_116, h_117⟩
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_292)
    have h_292 : Litex.In _value_i5 (Litex.R (M := M)) := h_292
    have h_116 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i5 = (M.number (1 : ℂ))))
              exact h_116)
          )
      )
    have h_117 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i5 = (M.number (0 : ℂ))))
              exact h_117)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _membership_function := (_object_i1 (M := M))
          let _membership_target := (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))) _raw_i5) → True := (by
              rintro _raw_i5 h_121 ⟨h_116, h_117⟩
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_121)
              have h_121 : Litex.In _value_i5 (Litex.R (M := M)) := h_121
              have h_116 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i5 = (M.number (1 : ℂ))))
                        exact h_116)
                    )
                )
              have h_117 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i5 = (M.number (0 : ℂ))))
                        exact h_117)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ)))))))))
          have h_129 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_142 : Litex.In _value_i6 (Litex.R (M := M))) (h_124 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))) (h_125 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (1 : ℂ))), ((Litex.In _value_i6 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i6 (Litex.number (M := M) (1 : ℂ))) ∧ (¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)))))) := (by
            intro _Host_i6 _rep_i6 _value_i6 h_142 h_124 h_125
            have h_126 : Litex.In _value_i6 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_142
                  )
              )
            have h_127 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_125
                  )
              )
            have h_128 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_124
                  )
              )
            exact (And.intro h_126 (And.intro h_127 h_128))
          )
          have h_166 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_179 : Litex.In _value_i7 (Litex.R (M := M))) (h_161 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (1 : ℂ))) (h_162 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ))), ((Litex.In _value_i7 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ))) ∧ (¬ Litex.Same _value_i7 (Litex.number (M := M) (1 : ℂ)))))) := (by
            intro _Host_i7 _rep_i7 _value_i7 h_179 h_161 h_162
            have h_163 : Litex.In _value_i7 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_179
                  )
              )
            have h_164 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_162
                  )
              )
            have h_165 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (1 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_161
                  )
              )
            exact (And.intro h_163 (And.intro h_164 h_165))
          )
          have h_119 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_210 : Litex.In _value_i5 (Litex.R (M := M))) (h_116 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ))) (h_117 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))), (by
            let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (_object_i1 (M := M)) _value_i5 (h_114 (M := M)) h_210 (And.intro h_117 h_116))
            exact (by
              let _atomic_wd_1_0 := _object_w25
              exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i5 _rep_i5 _value_i5 h_210 h_116 h_117
                    let _object_w25 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (_object_i1 (M := M)) _value_i5 (h_114 (M := M)) h_210 (And.intro h_117 h_116))
                    have h_120 : (by
                      let _atomic_wd_1_0 := _object_w25
                      exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := _object_w25
                              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))
                          )
                      )
                    exact h_120
                  )
                )
            )
          exact (by
          let _source_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))
          have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))) ((h_115 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
          have _same_domain : _source_signature.domain = _membership_target.val.domain := (Litex.SetSemantics.ext ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain_isSet ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))))).domain_isSet (fun x => ⟨fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))))).domain from by
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) _litex_input) _).mp _preimage_domain
          rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
          have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
          have _domain_target := h_129 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0 _preimage_guard_1
          have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
          exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(And.left _domain_target), (And.intro (And.left (And.right _domain_target)) (And.right (And.right _domain_target)))⟩)
        ) x hx, fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain from by
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.C (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (((¬ (_raw_i5 = (M.number (1 : ℂ))))) ∧ ((¬ (_raw_i5 = (M.number (0 : ℂ))))))) _litex_input) _).mp _preimage_domain
          rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
          have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
          have _domain_target := h_166 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0 _preimage_guard_1
          have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
          exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i2 = (M.number (1 : ℂ))))))) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(And.left _domain_target), (And.intro (And.left (And.right _domain_target)) (And.right (And.right _domain_target)))⟩)
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
          exact h_119 _arg_0 _member_0 (And.left _guard) (And.right _guard))
        )
      )
  )

noncomputable def _object_i8 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))) (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (M.divValue _raw_i9 _raw_i10)) (by
  rintro _raw_i9 _raw_i10 h_372 h_373 ⟨h_297, h_298⟩
  let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_372)
  have h_372 : Litex.In _value_i9 (Litex.R (M := M)) := h_372
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_373)
  have h_373 : Litex.In _value_i10 (Litex.R (M := M)) := h_373
  have h_297 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i10 = (M.number (0 : ℂ))))
            exact h_297)
        )
    )
  have h_298 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i9 = (M.number (0 : ℂ))))
            exact h_298)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div _value_i9 _value_i10 (M.real_subset_complex _ h_372) (M.real_subset_complex _ h_373) h_297)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div _value_i9 _value_i10 (M.real_subset_complex _ h_372) (M.real_subset_complex _ h_373) h_297)
    exact (Litex.divInR _value_i9 _value_i10 h_372 h_373 (_atomic_wd_1_0).wd.2.2))))
theorem h_491 : Litex.In (_object_i8 (M := M)) (Litex.fnSet ((_object_i8 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i8 (M := M)))
      )
  )
theorem h_492 : Litex.Same (_object_i8 (M := M)) (_object_i8 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i8 (M := M)))
      )
  )

theorem h_497 : (by
  let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i17 : M.Value) (_raw_i18 : M.Value), M.mem _raw_i17 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i18 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i17 : M.Value) (_raw_i18 : M.Value) => (((¬ (_raw_i17 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ))))))) _raw_i17 _raw_i18) → True := (by
      rintro _raw_i17 _raw_i18 h_749 h_750 ⟨h_495, h_496⟩
      let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_749)
      have h_749 : Litex.In _value_i17 (Litex.R (M := M)) := h_749
      let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_750)
      have h_750 : Litex.In _value_i18 (Litex.R (M := M)) := h_750
      have h_495 : ¬ Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i17 = (M.number (0 : ℂ))))
                exact h_495)
            )
        )
      have h_496 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i18 = (M.number (0 : ℂ))))
                exact h_496)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i17 : M.Value) (_raw_i18 : M.Value) => (((¬ (_raw_i17 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ)))))))))
  exact Litex.In (_object_i8 (M := M)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _membership_function := (_object_i8 (M := M))
          let _membership_target := (let _checked_header : ∀ (_raw_i15 : M.Value) (_raw_i16 : M.Value), M.mem _raw_i15 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i16 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ))))))) _raw_i15 _raw_i16) → True := (by
              rintro _raw_i15 _raw_i16 h_501 h_502 ⟨h_493, h_494⟩
              let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_501)
              have h_501 : Litex.In _value_i15 (Litex.R (M := M)) := h_501
              let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_502)
              have h_502 : Litex.In _value_i16 (Litex.R (M := M)) := h_502
              have h_493 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i15 = (M.number (0 : ℂ))))
                        exact h_493)
                    )
                )
              have h_494 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i16 = (M.number (0 : ℂ))))
                        exact h_494)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ)))))))))
          have h_510 : ∀ {_Host_i19 : Type _} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_523 : Litex.In _value_i19 (Litex.R (M := M))) {_Host_i20 : Type _} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (h_524 : Litex.In _value_i20 (Litex.R (M := M))) (h_504 : ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ))) (h_505 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ))), ((Litex.In _value_i19 (Litex.R (M := M))) ∧ (((Litex.In _value_i20 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ))) ∧ (¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)))))))) := (by
            intro _Host_i19 _rep_i19 _value_i19 h_523 _Host_i20 _rep_i20 _value_i20 h_524 h_504 h_505
            have h_506 : Litex.In _value_i19 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_523
                  )
              )
            have h_507 : Litex.In _value_i20 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_524
                  )
              )
            have h_508 : ¬ Litex.Same _value_i19 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_505
                  )
              )
            have h_509 : ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_504
                  )
              )
            exact (And.intro h_506 (And.intro h_507 (And.intro h_508 h_509)))
          )
          have h_552 : ∀ {_Host_i21 : Type _} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (h_565 : Litex.In _value_i21 (Litex.R (M := M))) {_Host_i22 : Type _} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (h_566 : Litex.In _value_i22 (Litex.R (M := M))) (h_546 : ¬ Litex.Same _value_i21 (Litex.number (M := M) (0 : ℂ))) (h_547 : ¬ Litex.Same _value_i22 (Litex.number (M := M) (0 : ℂ))), ((Litex.In _value_i21 (Litex.R (M := M))) ∧ (((Litex.In _value_i22 (Litex.R (M := M))) ∧ (((¬ Litex.Same _value_i22 (Litex.number (M := M) (0 : ℂ))) ∧ (¬ Litex.Same _value_i21 (Litex.number (M := M) (0 : ℂ)))))))) := (by
            intro _Host_i21 _rep_i21 _value_i21 h_565 _Host_i22 _rep_i22 _value_i22 h_566 h_546 h_547
            have h_548 : Litex.In _value_i21 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_565
                  )
              )
            have h_549 : Litex.In _value_i22 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_566
                  )
              )
            have h_550 : ¬ Litex.Same _value_i22 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_547
                  )
              )
            have h_551 : ¬ Litex.Same _value_i21 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_546
                  )
              )
            exact (And.intro h_548 (And.intro h_549 (And.intro h_550 h_551)))
          )
          have h_499 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_600 : Litex.In _value_i15 (Litex.R (M := M))) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_601 : Litex.In _value_i16 (Litex.R (M := M))) (h_493 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ))) (h_494 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ))), (by
            let _object_w52 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))) (_object_i8 (M := M)) _value_i15 _value_i16 (h_491 (M := M)) h_600 h_601 (And.intro h_494 h_493))
            exact (by
              let _atomic_wd_1_0 := _object_w52
              exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i15 _rep_i15 _value_i15 h_600 _Host_i16 _rep_i16 _value_i16 h_601 h_493 h_494
                    let _object_w52 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))) (_object_i8 (M := M)) _value_i15 _value_i16 (h_491 (M := M)) h_600 h_601 (And.intro h_494 h_493))
                    have h_500 : (by
                      let _atomic_wd_1_0 := _object_w52
                      exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := _object_w52
                              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0)))
                          )
                      )
                    exact h_500
                  )
                )
            )
          have h_498 : Litex.In (_object_i8 (M := M)) (let _checked_header : ∀ (_raw_i15 : M.Value) (_raw_i16 : M.Value), M.mem _raw_i15 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i16 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ))))))) _raw_i15 _raw_i16) → True := (by
              rintro _raw_i15 _raw_i16 h_742 h_743 ⟨h_493, h_494⟩
              let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_742)
              have h_742 : Litex.In _value_i15 (Litex.R (M := M)) := h_742
              let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_743)
              have h_743 : Litex.In _value_i16 (Litex.R (M := M)) := h_743
              have h_493 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i15 = (M.number (0 : ℂ))))
                        exact h_493)
                    )
                )
              have h_494 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i16 = (M.number (0 : ℂ))))
                        exact h_494)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ))))))))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _source_signature := (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))))
                    have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame (_object_i8 (M := M)) (_object_i8 (M := M)) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))))) ((h_492 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i8 (M := M))))
                    have _same_domain : _source_signature.domain = _membership_target.val.domain := (Litex.SetSemantics.ext ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))))).domain ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ))))))))).domain ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))))).domain_isSet ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ))))))))).domain_isSet (fun x => ⟨fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ))))))))).domain from by
                    intro _preimage_input _preimage_domain
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
                    have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
                    have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
                    rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
                    have _preimage_base : M.mem _preimage_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
                    have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
                    have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))
                    have _domain_target := h_510 (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)) (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0 _preimage_guard_1
                    have _repack : _preimage_input = (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))))) := (show _preimage_input = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ)))]) from (by
                    apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
                    apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
                    funext i
                    fin_cases i <;> norm_num [Litex.FiniteFunction.index]))
                    exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ))))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))))).mpr ⟨(And.left _domain_target), (And.left (And.right _domain_target)), (And.intro (And.left (And.right (And.right _domain_target))) (And.right (And.right (And.right _domain_target))))⟩)
                  ) x hx, fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ))))))))).domain → M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))))).domain from by
                    intro _preimage_input _preimage_domain
                    obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.C (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
                    have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
                    have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.isSet (Litex.C (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _preimage_domain
                    rcases _preimage_guard with ⟨_preimage_guard_0, _preimage_guard_1⟩
                    have _preimage_base : M.mem _preimage_input (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.R (M := M))), (Litex.denote (Litex.R (M := M)))]) := (Litex.FiniteFunction.cart_of_coordinates _preimage_members (by
                    have _finiteProof_0 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (0 : Fin 2)))
                    have _finiteProof_1 := ((by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members (1 : Fin 2)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))
                    have _domain_target := h_552 (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num)) (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))) (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)) _preimage_guard_0 _preimage_guard_1
                    have _repack : _preimage_input = (Litex.FiniteFunction.pack2 (M := M) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))))) := (show _preimage_input = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ)))]) from (by
                    apply (Litex.FiniteFunction.reconstruct _preimage_base).trans
                    apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
                    funext i
                    fin_cases i <;> norm_num [Litex.FiniteFunction.index]))
                    exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))))).domain) _repack) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (((¬ (_raw_i10 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i9 = (M.number (0 : ℂ))))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (1 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (0 : Fin 2) (1 : ℂ) (by norm_num))))) (Litex.denote (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) _preimage_input (M.number (2 : ℂ))) (M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base (1 : Fin 2) (2 : ℂ) (by norm_num)))))).mpr ⟨(And.left _domain_target), (And.left (And.right _domain_target)), (And.intro (And.left (And.right (And.right _domain_target))) (And.right (And.right (And.right _domain_target))))⟩)
                  ) x hx⟩))
                    change M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _membership_target.val.domain _membership_target.val.output)
                    have _source_graph : M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _source_signature.domain _source_signature.output) := _source_member
                    rw [_same_domain] at _source_graph
                    apply Litex.FunctionSemantics.fnSet_of_returns _source_graph
                    intro _input _hin
                    change M.mem _input (Litex.SetSemantics.sepValue _ _) at _hin
                    obtain ⟨_members, _guard⟩ := (Litex.SetSemantics.sep_members _ _ _).mp _hin
                    obtain ⟨_raw_0, _member_0, _raw_1, _member_1, rfl⟩ := (Litex.FiniteFunction.cart2_members _ _ _).mp _members
                    simp only [Litex.FiniteFunction.unpack_pack2] at _guard
                    let _arg_0 := Litex.semanticObject (M := M) _raw_0 (M.member_isSet _member_0)
                    let _arg_1 := Litex.semanticObject (M := M) _raw_1 (M.member_isSet _member_1)
                    exact h_499 _arg_0 _member_0 _arg_1 _member_1 (And.left _guard) (And.right _guard))
                )
            )
          exact (by
          let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i17 : M.Value) (_raw_i18 : M.Value), M.mem _raw_i17 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i18 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i17 : M.Value) (_raw_i18 : M.Value) => (((¬ (_raw_i17 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ))))))) _raw_i17 _raw_i18) → True := (by
              rintro _raw_i17 _raw_i18 h_749 h_750 ⟨h_495, h_496⟩
              let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_749)
              have h_749 : Litex.In _value_i17 (Litex.R (M := M)) := h_749
              let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_750)
              have h_750 : Litex.In _value_i18 (Litex.R (M := M)) := h_750
              have h_495 : ¬ Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i17 = (M.number (0 : ℂ))))
                        exact h_495)
                    )
                )
              have h_496 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i18 = (M.number (0 : ℂ))))
                        exact h_496)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i17 : M.Value) (_raw_i18 : M.Value) => (((¬ (_raw_i17 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i18 = (M.number (0 : ℂ)))))))))
          exact (Litex.inOfSame (_object_i8 (M := M)) (_object_i8 (M := M)) (let _checked_header : ∀ (_raw_i15 : M.Value) (_raw_i16 : M.Value), M.mem _raw_i15 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i16 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ))))))) _raw_i15 _raw_i16) → True := (by
              rintro _raw_i15 _raw_i16 h_742 h_743 ⟨h_493, h_494⟩
              let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_742)
              have h_742 : Litex.In _value_i15 (Litex.R (M := M)) := h_742
              let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_743)
              have h_743 : Litex.In _value_i16 (Litex.R (M := M)) := h_743
              have h_493 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i15 = (M.number (0 : ℂ))))
                        exact h_493)
                    )
                )
              have h_494 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i16 = (M.number (0 : ℂ))))
                        exact h_494)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ))))))))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
            let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i15 : M.Value) (_raw_i16 : M.Value), M.mem _raw_i15 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i16 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ))))))) _raw_i15 _raw_i16) → True := (by
              rintro _raw_i15 _raw_i16 h_742 h_743 ⟨h_493, h_494⟩
              let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_742)
              have h_742 : Litex.In _value_i15 (Litex.R (M := M)) := h_742
              let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_743)
              have h_743 : Litex.In _value_i16 (Litex.R (M := M)) := h_743
              have h_493 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i15 = (M.number (0 : ℂ))))
                        exact h_493)
                    )
                )
              have h_494 : ¬ Litex.Same _value_i16 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i16 = (M.number (0 : ℂ))))
                        exact h_494)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i15 : M.Value) (_raw_i16 : M.Value) => (((¬ (_raw_i15 = (M.number (0 : ℂ))))) ∧ ((¬ (_raw_i16 = (M.number (0 : ℂ)))))))))
            let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
            exact (show Litex.Same _left _right from rfl)) h_498))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_reordered_x5f_function_x5f_membership_x2f_statement_x2e_lit
