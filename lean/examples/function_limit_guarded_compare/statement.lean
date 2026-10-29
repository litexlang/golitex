import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_guarded_x5f_compare_x2f_statement_x2e_lit

universe u v1 v2 v5 v6 v7 v8 v9
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_11 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_14 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_14
    have h_15 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
      (by
        litex_checked_step =>
          exact (
            ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose
          )
      )
    have h_16 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
      (by
        litex_checked_step =>
          exact (
            ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose_spec
          )
      )
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_14 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_14
    have h_15 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
      (by
        litex_checked_step =>
          exact (
            ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose
          )
      )
    have h_16 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
      (by
        litex_checked_step =>
          exact (
            ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose_spec
          )
      )
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_19 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_20 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_21 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_22 : Litex.In _value_i8 (Litex.RPos (M := M))) (h_2 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_14 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_14
      have h_15 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
        (by
          litex_checked_step =>
            exact (
              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose
            )
        )
      have h_16 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
        (by
          litex_checked_step =>
            exact (
              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose_spec
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_14 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_14
      have h_15 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
        (by
          litex_checked_step =>
            exact (
              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose
            )
        )
      have h_16 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
        (by
          litex_checked_step =>
            exact (
              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose_spec
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_14 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_14
      have h_15 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
        (by
          litex_checked_step =>
            exact (
              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose
            )
        )
      have h_16 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
        (by
          litex_checked_step =>
            exact (
              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose_spec
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_17)
    have _limit_input : Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) (Litex.R (M := M)) := (by
    let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_27 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))
    exact (by
      let _set := _atomic_wd_2_0
      exact Litex.setBuilderSubset _set.val.bound _set.val.predicate))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_31 : Litex.In _value_i5 (Litex.R (M := M)) := h_19
  have h_40 : Litex.In _value_i6 (Litex.R (M := M)) := h_20
  exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i5 _value_i6)) (h_3 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_14 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_14
      have h_15 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
        (by
          litex_checked_step =>
            exact (
              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose
            )
        )
      have h_16 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
        (by
          litex_checked_step =>
            exact (
              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose_spec
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))).val
    have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_14 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_14
      have h_15 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
        (by
          litex_checked_step =>
            exact (
              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose
            )
        )
      have h_16 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
        (by
          litex_checked_step =>
            exact (
              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose_spec
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_14 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_14)
      have h_14 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_14
      have h_15 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
        (by
          litex_checked_step =>
            exact (
              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose
            )
        )
      have h_16 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
        (by
          litex_checked_step =>
            exact (
              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_14)).choose_spec
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_18)
    have _limit_input : Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_13 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) (Litex.R (M := M)) := (by
    let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_53 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))
    exact (by
      let _set := _atomic_wd_2_0
      exact Litex.setBuilderSubset _set.val.bound _set.val.predicate))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_57 : Litex.In _value_i5 (Litex.R (M := M)) := h_19
  have h_66 : Litex.In _value_i7 (Litex.R (M := M)) := h_21
  exact Litex.HasFiniteFunctionLimit .both _value_i2 _value_i5 _value_i7)) (h_9 : ∀ (_value_i9 : Litex.Obj (M := M) M.Value) (h_1558 : Litex.In _value_i9 (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_79 : Litex.In _value_i11 (Litex.R (M := M))) => ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_81 : Litex.In _value_i10 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_79 : Litex.In _value_i11 (Litex.R (M := M))) => ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))))) => (by
  have h_82 : (M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_79 : Litex.In _value_i11 (Litex.R (M := M))) => ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i10 _litex_builder).mp h_81)).choose
        )
    )
  exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i10 _value_i5 (M.real_subset_complex _ h_82) (M.real_subset_complex _ h_19));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i10 _value_i5 h_82 h_19))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i10 _value_i5 (M.real_subset_complex _ h_82) (M.real_subset_complex _ h_19));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR _value_i10 _value_i5 h_82 h_19)))) _value_i8))
)))), (by
  have h_1559 : (M.mem (Litex.denote _value_i9) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i11 : M.Value) => ∃ (_ : M.mem _raw_i11 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i11 = (M.number (0 : ℂ))))))) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_79 : Litex.In _value_i11 (Litex.R (M := M))) => ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_81 : Litex.In _value_i10 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_79 : Litex.In _value_i11 (Litex.R (M := M))) => ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))))) => (by
            have h_82 : (M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) :=
              (by
                litex_checked_step =>
                  exact (
                    ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_79 : Litex.In _value_i11 (Litex.R (M := M))) => ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i10 _litex_builder).mp h_81)).choose
                  )
              )
            exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i10 _value_i5 (M.real_subset_complex _ h_82) (M.real_subset_complex _ h_19));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i10 _value_i5 h_82 h_19))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i10 _value_i5 (M.real_subset_complex _ h_82) (M.real_subset_complex _ h_19));
            (Litex.abs _wd_1_0 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.subInR _value_i10 _value_i5 h_82 h_19)))) _value_i8))
          ))); (Litex.inSetBuilderObj_iff _value_i9 _litex_builder).mp h_1558)).choose
        )
    )
  exact (by
    let _atomic_wd_1_0 := (let _litex_call_arg_0 := _value_i9;
    Litex.callOnDomain (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1564 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_17 (by
      let _atomic_wd_2_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1564 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))
      exact (Litex.inOfSame _value_i9 _value_i9 _atomic_wd_2_1 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left := _atomic_wd_2_1
        let _right := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_1559)) True.intro)
    let _atomic_wd_1_1 := (let _litex_call_arg_0 := _value_i9;
    Litex.callOnDomain (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1575 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_18 (by
      let _atomic_wd_2_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1575 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))
      exact (Litex.inOfSame _value_i9 _value_i9 _atomic_wd_2_1 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left := _atomic_wd_2_1
        let _right := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_1559)) True.intro)
    exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)
)), Litex.Le _value_i6 _value_i7 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 _Host_i5 _rep_i5 _value_i5 h_19 _Host_i6 _rep_i6 _value_i6 h_20 _Host_i7 _rep_i7 _value_i7 h_21 _Host_i8 _rep_i8 _value_i8 h_22 h_2 h_3 h_9
          have h_23 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i8 h_22)
                )
            )
          have h_24 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i8 h_23)
                )
            )
          have h_25 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i8 h_23) _litex_zero.symm)
                )
            )
          have h_1957 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_1954 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1954)
              have h_1954 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_1954
              have h_1955 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
                (by
                  litex_checked_step =>
                    exact (
                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose
                    )
                )
              have h_1956 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
                (by
                  litex_checked_step =>
                    exact (
                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose_spec
                    )
                )
              exact True.intro);
            Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) :=
            (by
              litex_checked_step =>
                exact (
                  h_17
                )
            )
          have h_1958 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_1954 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1954)
              have h_1954 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_1954
              have h_1955 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
                (by
                  litex_checked_step =>
                    exact (
                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose
                    )
                )
              have h_1956 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
                (by
                  litex_checked_step =>
                    exact (
                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose_spec
                    )
                )
              exact True.intro);
            Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) :=
            (by
              litex_checked_step =>
                exact (
                  h_18
                )
            )
          have h_1959 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_19
                )
            )
          have h_1960 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_20
                )
            )
          have h_1961 : Litex.In _value_i7 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_21
                )
            )
          have h_1962 : Litex.In _value_i8 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_22
                )
            )
          have h_1963 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i8 h_1962)
                )
            )
          have h_1964 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i8 h_1963)
                )
            )
          have h_1965 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i8 h_1963) _litex_zero.symm)
                )
            )
          have h_12 : Litex.Le _value_i6 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_3873 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_1954 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1954)
                          have h_1954 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_1954
                          have h_1955 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose
                                )
                            )
                          have h_1956 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose_spec
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_1954 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1954)
                                  have h_1954 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_1954
                                  have h_1955 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose
                                        )
                                    )
                                  have h_1956 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose_spec
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
                              exact h_1957)
                          )
                      )
                    have h_3874 : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))
                      exact Litex.Subset _atomic_wd_1_0 (Litex.R (M := M))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))
                              exact (by
                                let _set := _atomic_wd_1_0
                                exact Litex.setBuilderSubset _set.val.bound _set.val.predicate))
                          )
                      )
                    have h_3875 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_3876 : Litex.In _value_i5 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1959
                          )
                      )
                    have h_3882 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_1954 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1954)
                          have h_1954 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_1954
                          have h_1955 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose
                                )
                            )
                          have h_1956 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose_spec
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_1954 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1954)
                                  have h_1954 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_1954
                                  have h_1955 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose
                                        )
                                    )
                                  have h_1956 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
                                    (by
                                      litex_checked_step =>
                                        exact (
                                          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose_spec
                                        )
                                    )
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
                              exact h_1958)
                          )
                      )
                    have h_3883 : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))
                      exact Litex.Subset _atomic_wd_1_0 (Litex.R (M := M))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))
                              exact h_3874)
                          )
                      )
                    have h_3884 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3875
                          )
                      )
                    have h_3885 : (by
                      let _equal_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))
                      let _equal_wd_1_1 := _equal_wd_1_0
                      exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_3886 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i5 _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    have h_3887 : Litex.HasFiniteFunctionLimit .both _value_i2 _value_i5 _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3
                          )
                      )
                    have h_3888 : Litex.In _value_i8 (Litex.RPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1962
                          )
                      )
                    have h_3981 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i8 h_3888)
                          )
                      )
                    have h_3982 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i8 h_3981)
                          )
                      )
                    have h_3983 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i8 h_3981) _litex_zero.symm)
                          )
                      )
                    have h_3893 : ∀ {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_6470 : Litex.In _value_i14 (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_3989 : Litex.In _value_i13 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) => (by
                      have h_3990 : (M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i13 _litex_builder).mp h_3989)).choose
                            )
                        )
                      exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i13 _value_i5 (M.real_subset_complex _ h_3990) (M.real_subset_complex _ h_3876));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR _value_i13 _value_i5 h_3990 h_3876))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i13 _value_i5 (M.real_subset_complex _ h_3990) (M.real_subset_complex _ h_3876));
                      (Litex.abs _wd_1_0 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.subInR _value_i13 _value_i5 h_3990 h_3876)))) _value_i8))
                    )))), (by
                      have h_6471 : (M.mem (Litex.denote _value_i14) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i3 : M.Value) => ∃ (_ : M.mem _raw_i3 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i3 = (M.number (0 : ℂ))))))) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_3989 : Litex.In _value_i13 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_3990 : (M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i13 _litex_builder).mp h_3989)).choose
                                      )
                                  )
                                exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i13 _value_i5 (M.real_subset_complex _ h_3990) (M.real_subset_complex _ h_3876));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.subInR _value_i13 _value_i5 h_3990 h_3876))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i13 _value_i5 (M.real_subset_complex _ h_3990) (M.real_subset_complex _ h_3876));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.subInR _value_i13 _value_i5 h_3990 h_3876)))) _value_i8))
                              ))); (Litex.inSetBuilderObj_iff _value_i14 _litex_builder).mp h_6470)).choose
                            )
                        )
                      exact Litex.Le (let _litex_call_arg_0 := _value_i14;
                      Litex.callOnDomain (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_3873 (by
                        let _atomic_wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))
                        exact h_6471) True.intro) (let _litex_call_arg_0 := _value_i14;
                      Litex.callOnDomain (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_3882 (by
                        let _atomic_wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))
                        exact h_6471) True.intro)
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i14 _rep_i14 _value_i14 h_6470
                              have h_6471 : (M.mem (Litex.denote _value_i14) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i3 : M.Value) => ∃ (_ : M.mem _raw_i3 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i3 = (M.number (0 : ℂ))))))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_3989 : Litex.In _value_i13 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) => (by
                                        have h_3990 : (M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) :=
                                          (by
                                            litex_checked_step =>
                                              exact (
                                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i13 _litex_builder).mp h_3989)).choose
                                              )
                                          )
                                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i13 _value_i5 (M.real_subset_complex _ h_3990) (M.real_subset_complex _ h_3876));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i13 _value_i5 h_3990 h_3876))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i13 _value_i5 (M.real_subset_complex _ h_3990) (M.real_subset_complex _ h_3876));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i13 _value_i5 h_3990 h_3876)))) _value_i8))
                                      ))); (Litex.inSetBuilderObj_iff _value_i14 _litex_builder).mp h_6470)).choose
                                    )
                                )
                              have h_6474 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i14) (Litex.denote _value_i5))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i14) (Litex.denote _value_i5))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i8) = M.number (_s : ℂ) ∧ _r < _s))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_3989 : Litex.In _value_i13 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) => (by
                                        have h_3990 : (M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) :=
                                          (by
                                            litex_checked_step =>
                                              exact (
                                                ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i13 _litex_builder).mp h_3989)).choose
                                              )
                                          )
                                        exact ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i13 _value_i5 (M.real_subset_complex _ h_3990) (M.real_subset_complex _ h_3876));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i13 _value_i5 h_3990 h_3876))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i13 _value_i5 (M.real_subset_complex _ h_3990) (M.real_subset_complex _ h_3876));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR _value_i13 _value_i5 h_3990 h_3876)))) _value_i8))
                                      ))); (Litex.inSetBuilderObj_iff _value_i14 _litex_builder).mp h_6470)).choose_spec
                                    )
                                )
                              have h_6472 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_3989 : Litex.In _value_i13 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_3990 : (M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i13 _litex_builder).mp h_3989)).choose
                                      )
                                  )
                                have h_3991 : (¬ ((Litex.denote _value_i13) = (M.number (0 : ℂ)))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i13 _litex_builder).mp h_3989)).choose_spec
                                      )
                                  )
                                exact (let _wd_1_0 := (Litex.sub _value_i13 _value_i5 (M.real_subset_complex _ h_3990) (M.real_subset_complex _ h_3876));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i13 _value_i5 h_3990 h_3876))))
                              )) (Litex.semanticObject (Litex.denote _value_i14) (Litex.isSet _value_i14)) h_6471) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.left h_6474)
                                    )
                                )
                              have h_6473 : Litex.Lt ((fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_3989 : Litex.In _value_i13 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) => (by
                                have h_3990 : (M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i13 _litex_builder).mp h_3989)).choose
                                      )
                                  )
                                have h_3991 : (¬ ((Litex.denote _value_i13) = (M.number (0 : ℂ)))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i13 _litex_builder).mp h_3989)).choose_spec
                                      )
                                  )
                                exact (let _wd_1_0 := (Litex.sub _value_i13 _value_i5 (M.real_subset_complex _ h_3990) (M.real_subset_complex _ h_3876));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i13 _value_i5 h_3990 h_3876))))
                              )) (Litex.semanticObject (Litex.denote _value_i14) (Litex.isSet _value_i14)) h_6471) _value_i8 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.right h_6474)
                                    )
                                )
                              exact (h_9 (Litex.semanticObject (Litex.denote _value_i14) (Litex.isSet _value_i14)) h_6470)
                            )
                          )
                      )
                    have h_3894 : Litex.Le _value_i6 _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show Litex.Le _value_i6 _value_i7 from (by
                              let _law0_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                intro _raw_i4 h_1954 _
                                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1954)
                                have h_1954 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_1954
                                have h_1955 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose
                                      )
                                  )
                                have h_1956 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose_spec
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))).val
                              have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_3873
                              let _law0_source_domain := (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i3 : M.Value) => ∃ (_ : M.mem _raw_i3 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i3 = (M.number (0 : ℂ))))))
                              have _law0_domain_set : M.isSet _law0_source_domain := (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))))
                              have _law0_domain_match : _law0_source_domain = _law0_signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _law0_domain_set _law0_signature.domain_isSet
                                intro x
                                change M.mem x (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (fun _ => True))
                                rw [Litex.SetSemantics.sep_members]
                                exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                              let _law0_domain := Litex.semanticObject _law0_source_domain _law0_domain_set
                              have _law_real_0 : Litex.RealFunctionValue M (Litex.denote _value_i1) := by
                                refine ⟨_law0_signature, _law0_member, ?_, h_3875⟩
                                intro x hx
                                exact h_3874 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                              let _law1_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                intro _raw_i4 h_1954 _
                                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1954)
                                have h_1954 : Litex.In _value_i4 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) := h_1954
                                have h_1955 : (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose
                                      )
                                  )
                                have h_1956 : (¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ)))) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))); (Litex.inSetBuilderObj_iff _value_i4 _litex_builder).mp h_1954)).choose_spec
                                      )
                                  )
                                exact True.intro);
                              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.denote _litex_output) (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_1953 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))).val
                              have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_3882
                              let _law1_source_domain := (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_raw_i3 : M.Value) => ∃ (_ : M.mem _raw_i3 (M.standard Litex.StandardSetValue.real)), (¬ (_raw_i3 = (M.number (0 : ℂ))))))
                              have _law1_domain_set : M.isSet _law1_source_domain := (Litex.isSet (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))))
                              have _law1_domain_match : _law1_source_domain = _law1_signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _law1_domain_set _law1_signature.domain_isSet
                                intro x
                                change M.mem x (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_3899 : Litex.In _value_i3 (Litex.R (M := M))) => ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))))) (fun _ => True))
                                rw [Litex.SetSemantics.sep_members]
                                exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                              let _law1_domain := Litex.semanticObject _law1_source_domain _law1_domain_set
                              have _law_real_1 : Litex.RealFunctionValue M (Litex.denote _value_i2) := by
                                refine ⟨_law1_signature, _law1_member, ?_, h_3884⟩
                                intro x hx
                                exact h_3883 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                              exact Litex.finiteFunctionLimitCompare .both (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i5) (Litex.denote _value_i6) (Litex.denote _value_i7) (Litex.denote _law0_domain) _value_i8 h_3888 _law_domain_0 (_law_domain_1.symm.trans (h_3885.trans _law_domain_0)) h_3886 h_3887 (by
                                intro input hinput
                                exact h_3893 (Litex.semanticObject input (M.member_isSet hinput)) hinput
                              )
                            ))
                          )
                      )
                    exact h_3894
                  )
                )
            )
          exact h_12
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_guarded_x5f_compare_x2f_statement_x2e_lit
