import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_piecewise_x5f_total_x5f_reciprocal_x2f_statement_x2e_lit

universe u v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (show Litex.Obj (M := M) (Litex.PiecewiseFn M) from by
  let _signature := ((show Litex.Obj (M := M) (Litex.FunctionSignature M) from (by
    have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := by
      intro _raw_i2 h_3 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3)
      have h_3 : Litex.In _value_i2 (Litex.R (M := M)) := h_3
      exact True.intro
    exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))))).val
  let _branch_0 := (⟨(fun (_input : M.Value) => (_input = (M.number (0 : ℂ)))), (fun (_input : M.Value) => (M.number (0 : ℂ)))⟩ : Litex.FunctionBranch M)
  let _branch_1 := (⟨(fun (_input : M.Value) => (¬ (_input = (M.number (0 : ℂ))))), (fun (_input : M.Value) => (M.divValue (M.number (1 : ℂ)) _input))⟩ : Litex.FunctionBranch M)
  have _coverage : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → (((_raw_i2 = (M.number (0 : ℂ)))) ∨ ((¬ (_raw_i2 = (M.number (0 : ℂ)))))) := (by
    intro _raw_i2 h_4 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4)
    have h_4 : Litex.In _value_i2 (Litex.R (M := M)) := h_4
    exact (Classical.em (Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)))))
  have _apart_0_1 : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → ((_raw_i2 = (M.number (0 : ℂ)))) → ((¬ (_raw_i2 = (M.number (0 : ℂ))))) → False := (by
    intro _raw_i2 h_4 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4)
    have h_4 : Litex.In _value_i2 (Litex.R (M := M)) := h_4
    have h_6 := h_4
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
    have h_6 : Litex.In _value_i2 (Litex.R (M := M)) := h_6
    intro h_1 _other
    have h_1 : (_raw_i2 = (M.number (0 : ℂ))) := h_1
    have _excluded : Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) := h_1
    exact (_other _excluded))
  have _return_0 : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → ((_raw_i2 = (M.number (0 : ℂ)))) → ((M.mem (M.number (0 : ℂ)) (M.standard Litex.StandardSetValue.real))) := (by
    intro _raw_i2 h_4 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4)
    have h_4 : Litex.In _value_i2 (Litex.R (M := M)) := h_4
    have h_9 := h_4
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_9)
    have h_9 : Litex.In _value_i2 (Litex.R (M := M)) := h_9
    intro h_1
    have h_1 : (_raw_i2 = (M.number (0 : ℂ))) := h_1
    have _formed_body := (Litex.number (M := M) (0 : ℂ))
    exact (Litex.inOfSame _value_i2 (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_1 (show @Eq M.Value _ _ from Eq.refl _) h_9))
  have _return_1 : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → ((¬ (_raw_i2 = (M.number (0 : ℂ))))) → ((M.mem (M.divValue (M.number (1 : ℂ)) _raw_i2) (M.standard Litex.StandardSetValue.real))) := (by
    intro _raw_i2 h_4 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4)
    have h_4 : Litex.In _value_i2 (Litex.R (M := M)) := h_4
    have h_15 := h_4
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i2 (Litex.R (M := M)) := h_15
    intro h_2
    have h_2 : (¬ (_raw_i2 = (M.number (0 : ℂ)))) := h_2
    have _formed_body := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_15) h_2)
    exact (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_15) h_2)
      exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_15 (_atomic_wd_1_0).wd.2.2)))
  apply Litex.piecewiseFn _signature [_branch_0, _branch_1]
  refine ⟨?_, ?_, ?_⟩
  · intro _input _input_member
    obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _input).mp _input_member
    rcases _coverage _input _members _domain with _case | _case
    · exact ⟨_branch_0, (List.mem_cons_self), _case⟩
    · exact ⟨_branch_1, (List.mem_cons_of_mem _ (List.mem_cons_self)), _case⟩
  · exact (List.Pairwise.cons (by
    intro _branch _member
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _input).mp _input_member
      rintro ⟨_left, _right⟩
      exact _apart_0_1 _input _members _domain _left _right)
    cases _member) (List.Pairwise.cons (by
    intro _branch _member
    cases _member) List.Pairwise.nil))
  · exact (by
    intro _branch _member
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member _case
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _input).mp _input_member
      exact _return_0 _input _members _domain _case)
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member _case
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _input).mp _input_member
      exact _return_1 _input _members _domain _case)
    cases _member))

theorem h_63 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.piecewiseFnInFnSet (_object_i1 (M := M)))
      )
  )

theorem h_65 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9 : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) (h_1 : ((Litex.denote _value_i2) = (M.number (0 : ℂ)))), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i2)) = (M.number (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_9 h_1
          have _case_domain : M.mem (Litex.denote _value_i2) ((_object_i1 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) (Litex.denote _value_i2)).mpr ⟨h_9, (Eq.mpr rfl (True.intro : (fun (_raw_i2 : M.Value) => True) (Litex.denote _value_i2)))⟩
          exact (Litex.piecewiseFn_call_eq (_object_i1 (M := M)) (⟨(fun (_input : M.Value) => (fun (_raw_i2 : M.Value) => (_raw_i2 = (M.number (0 : ℂ)))) _input), (fun (_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.number (0 : ℂ))) _input)⟩ : Litex.FunctionBranch M) (List.mem_cons_self) (Litex.denote _value_i2) _case_domain (Eq.mpr rfl (h_1 : (fun (_raw_i2 : M.Value) => (_raw_i2 = (M.number (0 : ℂ)))) (Litex.denote _value_i2)))).trans rfl)
      )
  )

theorem h_67 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_15 : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) (h_2 : (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i2)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_15 h_2
          have _case_domain : M.mem (Litex.denote _value_i2) ((_object_i1 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) (Litex.denote _value_i2)).mpr ⟨h_15, (Eq.mpr rfl (True.intro : (fun (_raw_i2 : M.Value) => True) (Litex.denote _value_i2)))⟩
          exact (Litex.piecewiseFn_call_eq (_object_i1 (M := M)) (⟨(fun (_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _input), (fun (_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _input)⟩ : Litex.FunctionBranch M) (List.mem_cons_of_mem _ (List.mem_cons_self)) (Litex.denote _value_i2) _case_domain (Eq.mpr rfl (h_2 : (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (Litex.denote _value_i2)))).trans rfl)
      )
  )

noncomputable def _object_w10 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_63 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)

noncomputable def _object_w11 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_68 : (by
  let _equal_wd_1_0 := (_object_w10 (M := M))
  let _equal_wd_1_1 := (_object_w11 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w10 (M := M));
        let _equal_wd_1_1 := (_object_w11 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
          let _checked_call := _equal_wd_1_0
          let _case_arg_0 := (Litex.number (M := M) (2 : ℂ))
          have _case_requirement_0 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          have _checked_case_guard : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
          have _selected_beta := (h_67 (M := M)) _case_arg_0 _case_requirement_0 _checked_case_guard
          exact _selected_beta.trans (show @Eq M.Value _ _ from Eq.refl _))))
      )
  )

noncomputable def _object_w12 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_63 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) True.intro)

theorem h_216 : (by
  let _equal_wd_1_0 := (_object_w12 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w12 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (by
          let _checked_call := _equal_wd_1_0
          let _case_arg_0 := (Litex.number (M := M) (0 : ℂ))
          have _case_requirement_0 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
          have _checked_case_guard : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
          have _selected_beta := (h_65 (M := M)) _case_arg_0 _case_requirement_0 _checked_case_guard
          exact _selected_beta.trans (show @Eq M.Value _ _ from Eq.refl _))))
      )
  )

theorem h_243 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_247 : Litex.In _value_i3 (Litex.R (M := M))) (h_241 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_63 (M := M)) h_247 True.intro) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_247) h_241) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_247 h_241
          exact ((h_67 (M := M)) _value_i3 h_247 h_241)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_piecewise_x5f_total_x5f_reciprocal_x2f_statement_x2e_lit
