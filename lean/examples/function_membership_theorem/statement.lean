import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_membership_x5f_theorem_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_1 : Litex.In (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
  intro _raw_i1 h_130 _
  let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_130)
  have h_130 : Litex.In _value_i1 (Litex.R (M := M)) := h_130
  change Litex.In _value_i1 (Litex.R (M := M))
  exact h_130)) (by
  have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := by
    intro _raw_i2 h_136 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_136)
    have h_136 : Litex.In _value_i2 (Litex.R (M := M)) := h_136
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True))) :=
  (by
    let _membership_function := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
      intro _raw_i1 h_17 _
      let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_17)
      have h_17 : Litex.In _value_i1 (Litex.R (M := M)) := h_17
      change Litex.In _value_i1 (Litex.R (M := M))
      exact h_17))
    let _membership_target := (by
      have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := by
        intro _raw_i2 h_23 _
        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23)
        have h_23 : Litex.In _value_i2 (Litex.R (M := M)) := h_23
        exact True.intro
      exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True)))
    have h_2 : ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_36 : Litex.In _value_i2 (Litex.R (M := M))), (by
      let _object_w4 := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
        intro _raw_i1 h_50 _
        let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_50)
        have h_50 : Litex.In _value_i1 (Litex.R (M := M)) := h_50
        change Litex.In _value_i1 (Litex.R (M := M))
        exact h_50));
      let _wd_1_1 := _value_i2;
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_36 True.intro))
      exact (by
        let _atomic_wd_1_0 := _object_w4
        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
    ) :=
      (by
        litex_checked_step =>
          exact (
            (by
              intro _Host_i2 _rep_i2 _value_i2 h_36
              let _object_w4 := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
                intro _raw_i1 h_50 _
                let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_50)
                have h_50 : Litex.In _value_i1 (Litex.R (M := M)) := h_50
                change Litex.In _value_i1 (Litex.R (M := M))
                exact h_50));
              let _wd_1_1 := _value_i2;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_36 True.intro))
              have h_3 : (by
                let _atomic_wd_1_0 := _object_w4
                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        let _atomic_wd_1_0 := _object_w4
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))
                    )
                )
              exact h_3
            )
          )
      )
    exact (by
    let _source_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True))
    have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
    intro _raw_i1 h_110 _
    let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_110)
    have h_110 : Litex.In _value_i1 (Litex.R (M := M)) := h_110
    change Litex.In _value_i1 (Litex.R (M := M))
    exact h_110)) _membership_function (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
    intro _raw_i1 h_110 _
    let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_110)
    have h_110 : Litex.In _value_i1 (Litex.R (M := M)) := h_110
    change Litex.In _value_i1 (Litex.R (M := M))
    exact h_110))))
    have _same_domain : _source_signature.domain = _membership_target.val.domain := rfl
    let _target := (by
    have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := by
      intro _raw_i2 h_116 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_116)
      have h_116 : Litex.In _value_i2 (Litex.R (M := M)) := h_116
      exact True.intro
    exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i2 : M.Value) => True)))
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
    exact h_2 _arg_0 _member_0)
  )

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
  intro _raw_i4 h_179 h_137
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_179)
  have h_179 : Litex.In _value_i4 (Litex.R (M := M)) := h_179
  have h_137 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i4 = (M.number (0 : ℂ))))
            exact h_137)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_179) h_137)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_179) h_137)
    exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_179 (_atomic_wd_1_0).wd.2.2))))
theorem h_243 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_244 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (Litex.sameRefl (_object_i3 (M := M)))

theorem h_247 : (by
  let _atomic_wd_1_1 := (by
    have _checked_header : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) _raw_i7) → True := by
      intro _raw_i7 h_354 h_246
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_354)
      have h_354 : Litex.In _value_i7 (Litex.R (M := M)) := h_354
      have h_246 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i7 = (M.number (0 : ℂ))))
                exact h_246)
            )
        )
      exact True.intro
    exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ)))))))
  exact Litex.In (_object_i3 (M := M)) _atomic_wd_1_1) :=
  (by
    let _membership_function := (_object_i3 (M := M))
    let _membership_target := (by
      have _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := by
        intro _raw_i6 h_251 h_245
        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_251)
        have h_251 : Litex.In _value_i6 (Litex.R (M := M)) := h_251
        have h_245 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                  exact h_245)
              )
          )
        exact True.intro
      exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ)))))))
    have h_249 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_264 : Litex.In _value_i6 (Litex.R (M := M))) (h_245 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))), (by
      let _object_w23 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_243 (M := M)) h_264 h_245)
      exact (by
        let _atomic_wd_1_0 := _object_w23
        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
    ) :=
      (by
        litex_checked_step =>
          exact (
            (by
              intro _Host_i6 _rep_i6 _value_i6 h_264 h_245
              let _object_w23 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_243 (M := M)) h_264 h_245)
              have h_250 : (by
                let _atomic_wd_1_0 := _object_w23
                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        let _atomic_wd_1_0 := _object_w23
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))
                    )
                )
              exact h_250
            )
          )
      )
    have h_248 : Litex.In (_object_i3 (M := M)) (by
      have _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := by
        intro _raw_i6 h_350 h_245
        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_350)
        have h_350 : Litex.In _value_i6 (Litex.R (M := M)) := h_350
        have h_245 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                  exact h_245)
              )
          )
        exact True.intro
      exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _source_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))
              have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame (_object_i3 (M := M)) _membership_function (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) ((h_244 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M))))
              have _same_domain : _source_signature.domain = _membership_target.val.domain := rfl
              let _target := (by
              have _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := by
                intro _raw_i6 h_350 h_245
                let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_350)
                have h_350 : Litex.In _value_i6 (Litex.R (M := M)) := h_350
                have h_245 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                          exact h_245)
                      )
                  )
                exact True.intro
              exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ)))))))
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
              exact h_249 _arg_0 _member_0 _guard)
          )
      )
    exact (by
    let _atomic_wd_1_1 := (by
      have _checked_header : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) _raw_i7) → True := by
        intro _raw_i7 h_354 h_246
        let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_354)
        have h_354 : Litex.In _value_i7 (Litex.R (M := M)) := h_354
        have h_246 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  change (¬ (_raw_i7 = (M.number (0 : ℂ))))
                  exact h_246)
              )
          )
        exact True.intro
      exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ)))))))
    exact (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (by
      have _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := by
        intro _raw_i6 h_350 h_245
        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_350)
        have h_350 : Litex.In _value_i6 (Litex.R (M := M)) := h_350
        have h_245 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                  exact h_245)
              )
          )
        exact True.intro
      exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (by
      have _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := by
        intro _raw_i6 h_350 h_245
        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_350)
        have h_350 : Litex.In _value_i6 (Litex.R (M := M)) := h_350
        have h_245 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                  exact h_245)
              )
          )
        exact True.intro
      exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ)))))))
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_248))
  )

theorem h_363 : Litex.In (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.divValue _raw_i8 _raw_i9)) (by
  intro _raw_i8 _raw_i9 h_1226 h_1227 h_361
  let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1226)
  have h_1226 : Litex.In _value_i8 (Litex.R (M := M)) := h_1226
  let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1227)
  have h_1227 : Litex.In _value_i9 (Litex.R (M := M)) := h_1227
  have h_361 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i9 = (M.number (0 : ℂ))))
            exact h_361)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div _value_i8 _value_i9 (M.real_subset_complex _ h_1226) (M.real_subset_complex _ h_1227) h_361)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div _value_i8 _value_i9 (M.real_subset_complex _ h_1226) (M.real_subset_complex _ h_1227) h_361)
    exact (Litex.divInR _value_i8 _value_i9 h_1226 h_1227 (_atomic_wd_1_0).wd.2.2)))) (by
  have _checked_header : ∀ (_raw_i10 : M.Value) (_raw_i11 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _raw_i10 _raw_i11) → True := by
    intro _raw_i10 _raw_i11 h_1357 h_1358 h_362
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1357)
    have h_1357 : Litex.In _value_i10 (Litex.R (M := M)) := h_1357
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1358)
    have h_1358 : Litex.In _value_i11 (Litex.R (M := M)) := h_1358
    have h_362 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i11 = (M.number (0 : ℂ))))
              exact h_362)
          )
      )
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))))) :=
  (by
    let _membership_function := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.divValue _raw_i8 _raw_i9)) (by
      intro _raw_i8 _raw_i9 h_433 h_434 h_361
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_433)
      have h_433 : Litex.In _value_i8 (Litex.R (M := M)) := h_433
      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_434)
      have h_434 : Litex.In _value_i9 (Litex.R (M := M)) := h_434
      have h_361 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i9 = (M.number (0 : ℂ))))
                exact h_361)
            )
        )
      change (by
        let _atomic_wd_1_0 := (Litex.div _value_i8 _value_i9 (M.real_subset_complex _ h_433) (M.real_subset_complex _ h_434) h_361)
        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.div _value_i8 _value_i9 (M.real_subset_complex _ h_433) (M.real_subset_complex _ h_434) h_361)
        exact (Litex.divInR _value_i8 _value_i9 h_433 h_434 (_atomic_wd_1_0).wd.2.2))))
    let _membership_target := (by
      have _checked_header : ∀ (_raw_i10 : M.Value) (_raw_i11 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _raw_i10 _raw_i11) → True := by
        intro _raw_i10 _raw_i11 h_564 h_565 h_362
        let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_564)
        have h_564 : Litex.In _value_i10 (Litex.R (M := M)) := h_564
        let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_565)
        have h_565 : Litex.In _value_i11 (Litex.R (M := M)) := h_565
        have h_362 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  change (¬ (_raw_i11 = (M.number (0 : ℂ))))
                  exact h_362)
              )
          )
        exact True.intro
      exact Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ)))))))
    have h_364 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_590 : Litex.In _value_i10 (Litex.R (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_591 : Litex.In _value_i11 (Litex.R (M := M))) (h_362 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))), (by
      let _object_w40 := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.divValue _raw_i8 _raw_i9)) (by
        intro _raw_i8 _raw_i9 h_659 h_660 h_361
        let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_659)
        have h_659 : Litex.In _value_i8 (Litex.R (M := M)) := h_659
        let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_660)
        have h_660 : Litex.In _value_i9 (Litex.R (M := M)) := h_660
        have h_361 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  change (¬ (_raw_i9 = (M.number (0 : ℂ))))
                  exact h_361)
              )
          )
        change (by
          let _atomic_wd_1_0 := (Litex.div _value_i8 _value_i9 (M.real_subset_complex _ h_659) (M.real_subset_complex _ h_660) h_361)
          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_1_0 := (Litex.div _value_i8 _value_i9 (M.real_subset_complex _ h_659) (M.real_subset_complex _ h_660) h_361)
          exact (Litex.divInR _value_i8 _value_i9 h_659 h_660 (_atomic_wd_1_0).wd.2.2))));
      let _wd_1_1 := _value_i10;
      let _wd_1_2 := _value_i11;
      (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_590 h_591 h_362))
      exact (by
        let _atomic_wd_1_0 := _object_w40
        exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
    ) :=
      (by
        litex_checked_step =>
          exact (
            (by
              intro _Host_i10 _rep_i10 _value_i10 h_590 _Host_i11 _rep_i11 _value_i11 h_591 h_362
              let _object_w40 := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.divValue _raw_i8 _raw_i9)) (by
                intro _raw_i8 _raw_i9 h_659 h_660 h_361
                let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_659)
                have h_659 : Litex.In _value_i8 (Litex.R (M := M)) := h_659
                let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_660)
                have h_660 : Litex.In _value_i9 (Litex.R (M := M)) := h_660
                have h_361 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          change (¬ (_raw_i9 = (M.number (0 : ℂ))))
                          exact h_361)
                      )
                  )
                change (by
                  let _atomic_wd_1_0 := (Litex.div _value_i8 _value_i9 (M.real_subset_complex _ h_659) (M.real_subset_complex _ h_660) h_361)
                  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.div _value_i8 _value_i9 (M.real_subset_complex _ h_659) (M.real_subset_complex _ h_660) h_361)
                  exact (Litex.divInR _value_i8 _value_i9 h_659 h_660 (_atomic_wd_1_0).wd.2.2))));
              let _wd_1_1 := _value_i10;
              let _wd_1_2 := _value_i11;
              (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) h_590 h_591 h_362))
              have h_365 : (by
                let _atomic_wd_1_0 := _object_w40
                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        let _atomic_wd_1_0 := _object_w40
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.call2InOutput _atomic_wd_1_0)))
                    )
                )
              exact h_365
            )
          )
      )
    exact (by
    let _source_signature := (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))))
    have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.divValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_1023 h_1024 h_361
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1023)
    have h_1023 : Litex.In _value_i8 (Litex.R (M := M)) := h_1023
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1024)
    have h_1024 : Litex.In _value_i9 (Litex.R (M := M)) := h_1024
    have h_361 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i9 = (M.number (0 : ℂ))))
              exact h_361)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.div _value_i8 _value_i9 (M.real_subset_complex _ h_1023) (M.real_subset_complex _ h_1024) h_361)
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.div _value_i8 _value_i9 (M.real_subset_complex _ h_1023) (M.real_subset_complex _ h_1024) h_361)
      exact (Litex.divInR _value_i8 _value_i9 h_1023 h_1024 (_atomic_wd_1_0).wd.2.2)))) _membership_function (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.divValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_1023 h_1024 h_361
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1023)
    have h_1023 : Litex.In _value_i8 (Litex.R (M := M)) := h_1023
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1024)
    have h_1024 : Litex.In _value_i9 (Litex.R (M := M)) := h_1024
    have h_361 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i9 = (M.number (0 : ℂ))))
              exact h_361)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.div _value_i8 _value_i9 (M.real_subset_complex _ h_1023) (M.real_subset_complex _ h_1024) h_361)
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.div _value_i8 _value_i9 (M.real_subset_complex _ h_1023) (M.real_subset_complex _ h_1024) h_361)
      exact (Litex.divInR _value_i8 _value_i9 h_1023 h_1024 (_atomic_wd_1_0).wd.2.2))))))
    have _same_domain : _source_signature.domain = _membership_target.val.domain := rfl
    let _target := (by
    have _checked_header : ∀ (_raw_i10 : M.Value) (_raw_i11 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _raw_i10 _raw_i11) → True := by
      intro _raw_i10 _raw_i11 h_1154 h_1155 h_362
      let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1154)
      have h_1154 : Litex.In _value_i10 (Litex.R (M := M)) := h_1154
      let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1155)
      have h_1155 : Litex.In _value_i11 (Litex.R (M := M)) := h_1155
      have h_362 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i11 = (M.number (0 : ℂ))))
                exact h_362)
            )
        )
      exact True.intro
    exact Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ)))))))
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
    exact h_364 _arg_0 _member_0 _arg_1 _member_1 _guard)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_membership_x5f_theorem_x2f_statement_x2e_lit
