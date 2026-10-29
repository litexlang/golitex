import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_guarded_x5f_multiply_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v6 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_8 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_11 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
    intro _raw_i4 h_10 h_1
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
    have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
    have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i4 = (M.number (0 : ℂ))))
              exact h_1)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_12 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
    intro _raw_i4 h_10 h_1
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
    have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
    have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i4 = (M.number (0 : ℂ))))
              exact h_1)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_13 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
    intro _raw_i4 h_10 h_1
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
    have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
    have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i4 = (M.number (0 : ℂ))))
              exact h_1)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_14 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_15 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_16 : Litex.In _value_i7 (Litex.R (M := M))) (h_2 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
      intro _raw_i4 h_10 h_1
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
      intro _raw_i4 h_10 h_1
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
      intro _raw_i4 h_10 h_1
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_11)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_19 : Litex.In _value_i5 (Litex.R (M := M)) := h_14
  have h_30 : Litex.In _value_i6 (Litex.R (M := M)) := h_15
  exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i5 _value_i6)) (h_3 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
      intro _raw_i4 h_10 h_1
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))).val
    have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
      intro _raw_i4 h_10 h_1
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
      intro _raw_i4 h_10 h_1
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_12)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_46 : Litex.In _value_i5 (Litex.R (M := M)) := h_14
  have h_57 : Litex.In _value_i7 (Litex.R (M := M)) := h_16
  exact Litex.HasFiniteFunctionLimit .both _value_i2 _value_i5 _value_i7)) (h_6 : ∀ (_value_i8 : Litex.Obj (M := M) M.Value) (h_73 : Litex.In _value_i8 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_72 : Litex.In _value_i9 (Litex.R (M := M))) => ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ))))), (by
  have h_74 : (M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_72 : Litex.In _value_i9 (Litex.R (M := M))) => ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i8 _litex_builder).mp h_73)).choose
        )
    )
  have h_75 : (¬ ((Litex.denote _value_i8) = (M.number (0 : ℂ)))) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_72 : Litex.In _value_i9 (Litex.R (M := M))) => ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i8 _litex_builder).mp h_73)).choose_spec
        )
    )
  exact (by
    let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _value_i3 _value_i8 h_13 h_74 h_75)
    let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _value_i1 _value_i8 h_11 h_74 h_75);
    let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _value_i2 _value_i8 h_12 h_74 h_75);
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
)), (by
  let _atomic_wd_1_2 := (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_15) (M.real_subset_complex _ h_16))
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i3) := (show Litex.RealFunctionValue M (Litex.denote _value_i3) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
      intro _raw_i4 h_10 h_1
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))).val
    have _limit_function : Litex.In _value_i3 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
      intro _raw_i4 h_10 h_1
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
      intro _raw_i4 h_10 h_1
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_13)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_561 : Litex.In _value_i5 (Litex.R (M := M)) := h_14
  have h_572 : (by
    let _atomic_wd_2_0 := _atomic_wd_1_2
    exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
    let _atomic_wd_2_0 := _atomic_wd_1_2
    exact (Litex.mulInR _value_i6 _value_i7 h_15 h_16))
  exact Litex.HasFiniteFunctionLimit .both _value_i3 _value_i5 _atomic_wd_1_2) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_11 _Host_i2 _rep_i2 _value_i2 h_12 _Host_i3 _rep_i3 _value_i3 h_13 _Host_i5 _rep_i5 _value_i5 h_14 _Host_i6 _rep_i6 _value_i6 h_15 _Host_i7 _rep_i7 _value_i7 h_16 h_2 h_3 h_6
          have h_673 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
              intro _raw_i4 h_672 h_1
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
              have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
              have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                        exact h_1)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_674 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
              intro _raw_i4 h_672 h_1
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
              have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
              have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                        exact h_1)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_675 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
              intro _raw_i4 h_672 h_1
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
              have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
              have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                        exact h_1)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          have h_676 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_14
                )
            )
          have h_677 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          have h_678 : Litex.In _value_i7 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_16
                )
            )
          have h_9 : (by
            let _atomic_wd_1_2 := (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_677) (M.real_subset_complex _ h_678))
            exact Litex.HasFiniteFunctionLimit .both _value_i3 _value_i5 _atomic_wd_1_2) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_1162 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
                          intro _raw_i4 h_672 h_1
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
                          have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
                          have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                    exact h_1)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
                                  intro _raw_i4 h_672 h_1
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
                                  have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
                                  have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (by
                                            change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                            exact h_1)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))
                              exact h_673)
                          )
                      )
                    have h_1163 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_1164 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1163
                          )
                      )
                    have h_1165 : Litex.In _value_i5 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_676
                          )
                      )
                    have h_1168 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
                          intro _raw_i4 h_672 h_1
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
                          have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
                          have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                    exact h_1)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
                                  intro _raw_i4 h_672 h_1
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
                                  have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
                                  have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (by
                                            change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                            exact h_1)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))
                              exact h_674)
                          )
                      )
                    have h_1169 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1163
                          )
                      )
                    have h_1170 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1163
                          )
                      )
                    have h_1171 : (by
                      let _equal_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_1233 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))
                      let _equal_wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_1234 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))
                      exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_1174 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
                          intro _raw_i4 h_672 h_1
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
                          have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
                          have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (by
                                    change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                    exact h_1)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))
                      exact Litex.In _value_i3 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
                                  intro _raw_i4 h_672 h_1
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
                                  have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
                                  have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (by
                                            change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                            exact h_1)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))
                              exact h_675)
                          )
                      )
                    have h_1175 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1163
                          )
                      )
                    have h_1176 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1163
                          )
                      )
                    have h_1177 : (by
                      let _equal_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_1234 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))
                      let _equal_wd_1_1 := _equal_wd_1_0
                      exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_1178 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i5 _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    have h_1179 : Litex.HasFiniteFunctionLimit .both _value_i2 _value_i5 _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3
                          )
                      )
                    have h_1181 : ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_1283 : Litex.In _value_i11 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_1234 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))))), (by
                      have h_1284 : (M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_1234 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i11 _litex_builder).mp h_1283)).choose
                            )
                        )
                      have h_1285 : (¬ ((Litex.denote _value_i11) = (M.number (0 : ℂ)))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_1234 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i11 _litex_builder).mp h_1283)).choose_spec
                            )
                        )
                      exact Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _value_i3 _value_i11 h_1174 h_1284 h_1285) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _value_i1 _value_i11 h_1162 h_1284 h_1285);
                      let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _value_i2 _value_i11 h_1168 h_1284 h_1285);
                      (Litex.mul _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
                        let _atomic_wd_1_0 := _wd_1_1
                        exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i11 _rep_i11 _value_i11 h_1283
                              have h_1284 : (M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_1234 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i11 _litex_builder).mp h_1283)).choose
                                    )
                                )
                              have h_1285 : (¬ ((Litex.denote _value_i11) = (M.number (0 : ℂ)))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_1234 : Litex.In _value_i4 (Litex.R (M := M))) => ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i11 _litex_builder).mp h_1283)).choose_spec
                                    )
                                )
                              exact (h_6 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) h_1283)
                            )
                          )
                      )
                    have h_1182 : Litex.HasFiniteFunctionLimit .both _value_i3 _value_i5 (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_677) (M.real_subset_complex _ h_678)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              let _atomic_wd_1_2 := (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_677) (M.real_subset_complex _ h_678))
                              have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i3) := (show Litex.RealFunctionValue M (Litex.denote _value_i3) from by
                                let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
                                  intro _raw_i4 h_672 h_1
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
                                  have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
                                  have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (by
                                            change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                            exact h_1)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))).val
                                have _limit_function : Litex.In _value_i3 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
                                  intro _raw_i4 h_672 h_1
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
                                  have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
                                  have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (by
                                            change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                            exact h_1)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
                                  intro _raw_i4 h_672 h_1
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
                                  have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
                                  have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          (by
                                            change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                            exact h_1)
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_1174)
                                have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_1163
                                have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_1163
                                refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                                intro x hx
                                exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              )
                              have h_1997 : Litex.In _value_i5 (Litex.R (M := M)) := h_1165
                              have h_2004 : (by
                                let _atomic_wd_2_0 := _atomic_wd_1_2
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
                                let _atomic_wd_2_0 := _atomic_wd_1_2
                                exact (Litex.mulInR _value_i6 _value_i7 h_677 h_678))
                              exact Litex.HasFiniteFunctionLimit .both _value_i3 _value_i5 _atomic_wd_1_2) from (by
                              let _law0_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
                                intro _raw_i4 h_672 h_1
                                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
                                have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
                                have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (by
                                          change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                          exact h_1)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))).val
                              have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_1162
                              let _law0_source_domain := (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i4 : M.Value) => ∃ (_ : M.mem _raw_i4 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i4 = (M.number (0 : ℂ))))))
                              have _law0_domain_set : M.isSet _law0_source_domain := (Litex.SetSemantics.sep_isSet (Litex.denote (Litex.R (M := M))) _ (Litex.isSet (Litex.R (M := M))))
                              have _law0_domain_match : _law0_source_domain = _law0_signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _law0_domain_set _law0_signature.domain_isSet
                                intro x
                                change M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _)
                                rw [Litex.SetSemantics.sep_members, Litex.SetSemantics.sep_members]
                                exact ⟨fun ⟨hx, _, hg⟩ => ⟨hx, hg⟩, fun ⟨hx, hg⟩ => ⟨hx, hx, hg⟩⟩
                              let _law0_domain := Litex.semanticObject _law0_source_domain _law0_domain_set
                              have _law_real_0 : Litex.RealFunctionValue M (Litex.denote _value_i1) := by
                                refine ⟨_law0_signature, _law0_member, ?_, h_1164⟩
                                intro x hx
                                exact h_1163 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                              let _law1_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
                                intro _raw_i4 h_672 h_1
                                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
                                have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
                                have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (by
                                          change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                          exact h_1)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))).val
                              have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_1168
                              let _law1_source_domain := (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i4 : M.Value) => ∃ (_ : M.mem _raw_i4 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i4 = (M.number (0 : ℂ))))))
                              have _law1_domain_set : M.isSet _law1_source_domain := (Litex.SetSemantics.sep_isSet (Litex.denote (Litex.R (M := M))) _ (Litex.isSet (Litex.R (M := M))))
                              have _law1_domain_match : _law1_source_domain = _law1_signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _law1_domain_set _law1_signature.domain_isSet
                                intro x
                                change M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _)
                                rw [Litex.SetSemantics.sep_members, Litex.SetSemantics.sep_members]
                                exact ⟨fun ⟨hx, _, hg⟩ => ⟨hx, hg⟩, fun ⟨hx, hg⟩ => ⟨hx, hx, hg⟩⟩
                              let _law1_domain := Litex.semanticObject _law1_source_domain _law1_domain_set
                              have _law_real_1 : Litex.RealFunctionValue M (Litex.denote _value_i2) := by
                                refine ⟨_law1_signature, _law1_member, ?_, h_1170⟩
                                intro x hx
                                exact h_1169 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                              let _law2_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
                                intro _raw_i4 h_672 h_1
                                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_672)
                                have h_672 : Litex.In _value_i4 (Litex.R (M := M)) := h_672
                                have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        (by
                                          change (¬ (_raw_i4 = (M.number (0 : ℂ))))
                                          exact h_1)
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))).val
                              have _law2_member : Litex.In _value_i3 (Litex.fnSet _law2_signature) := h_1174
                              let _law2_source_domain := (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i4 : M.Value) => ∃ (_ : M.mem _raw_i4 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i4 = (M.number (0 : ℂ))))))
                              have _law2_domain_set : M.isSet _law2_source_domain := (Litex.SetSemantics.sep_isSet (Litex.denote (Litex.R (M := M))) _ (Litex.isSet (Litex.R (M := M))))
                              have _law2_domain_match : _law2_source_domain = _law2_signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _law2_domain_set _law2_signature.domain_isSet
                                intro x
                                change M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) _)
                                rw [Litex.SetSemantics.sep_members, Litex.SetSemantics.sep_members]
                                exact ⟨fun ⟨hx, _, hg⟩ => ⟨hx, hg⟩, fun ⟨hx, hg⟩ => ⟨hx, hx, hg⟩⟩
                              let _law2_domain := Litex.semanticObject _law2_source_domain _law2_domain_set
                              have _law_real_2 : Litex.RealFunctionValue M (Litex.denote _value_i3) := by
                                refine ⟨_law2_signature, _law2_member, ?_, h_1176⟩
                                intro x hx
                                exact h_1175 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_2 : Litex.denote _law2_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i3) := (_law2_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law2_signature.domain_isSet _law2_member).symm)
                              exact Litex.finiteFunctionLimitMapTwo .both (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i3) (Litex.denote _value_i5) (Litex.denote _value_i6) (Litex.denote _value_i7) (Litex.denote (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_677) (M.real_subset_complex _ h_678))) _law_real_0 _law_real_1 _law_real_2 (_law_domain_1.symm.trans (h_1171.trans _law_domain_0)) (_law_domain_2.symm.trans (h_1177.trans _law_domain_0)) M.mulValue (fun x y : ℝ => x*y) (by intro x y; rw [M.mul_numbers, Complex.ofReal_mul]) rfl (by
                                intro input hinput
                                have _law_input : M.mem input (Litex.denote _law0_domain) := by
                                  rw [_law_domain_0]
                                  exact hinput
                                exact h_1181 (Litex.semanticObject input (M.member_isSet _law_input)) _law_input
                              ) (continuous_fst.mul continuous_snd) h_1178 h_1179
                            ))
                          )
                      )
                    exact (by
                    let _atomic_wd_1_2 := (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_677) (M.real_subset_complex _ h_678))
                    exact h_1182)
                  )
                )
            )
          exact (by
            let _atomic_wd_1_2 := (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_677) (M.real_subset_complex _ h_678))
            exact h_9)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_guarded_x5f_multiply_x5f_by_x5f_theorem_x2f_statement_x2e_lit
