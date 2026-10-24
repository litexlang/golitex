import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_piecewise_x5f_absolute_x5f_value_x2f_statement_x2e_lit

universe u v2
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
  let _branch_0 := (⟨(fun (_input : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _input = M.number (_s : ℂ) ∧ _r ≤ _s)), (fun (_input : M.Value) => _input)⟩ : Litex.FunctionBranch M)
  let _branch_1 := (⟨(fun (_input : M.Value) => (∃ (_r _s : ℝ), _input = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)), (fun (_input : M.Value) => (M.negValue _input))⟩ : Litex.FunctionBranch M)
  have _coverage : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s)) ∨ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))) := (by
    intro _raw_i2 h_4 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4)
    have h_4 : Litex.In _value_i2 (Litex.R (M := M)) := h_4
    exact (by
      have _split_member_0 : Litex.In _value_i2 (Litex.R (M := M)) := h_4
      have _split_member_1 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
      rcases lt_or_ge (Litex.NativeBridge.asReal _value_i2 _split_member_0) (Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) _split_member_1) with _lt | _ge
      · exact Or.inr ((Litex.NativeBridge.lt_iff_asReal _value_i2 (Litex.number (M := M) (0 : ℂ)) _split_member_0 _split_member_1).mpr _lt)
      · exact Or.inl ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _value_i2 _split_member_1 _split_member_0).mpr _ge)))
  have _apart_0_1 : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s)) → ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)) → False := (by
    intro _raw_i2 h_4 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4)
    have h_4 : Litex.In _value_i2 (Litex.R (M := M)) := h_4
    have h_30 := h_4
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_30)
    have h_30 : Litex.In _value_i2 (Litex.R (M := M)) := h_30
    intro h_1 _other
    have h_1 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s) := h_1
    have _excluded : ¬ Litex.Lt _value_i2 (Litex.number (M := M) (0 : ℂ)) := (by
      let _left := (Litex.number (M := M) (0 : ℂ))
      let _right := _value_i2
      have _leftReal : Litex.In _left Litex.R := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
      have _rightReal : Litex.In _right Litex.R := h_30
      exact fun _opposite => not_lt_of_ge ((Litex.NativeBridge.le_iff_asReal _left _right _leftReal _rightReal).mp h_1) ((Litex.NativeBridge.lt_iff_asReal _right _left _rightReal _leftReal).mp _opposite))
    exact (_excluded _other))
  have _return_0 : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s)) → ((M.mem _raw_i2 (M.standard Litex.StandardSetValue.real))) := (by
    intro _raw_i2 h_4 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4)
    have h_4 : Litex.In _value_i2 (Litex.R (M := M)) := h_4
    have h_81 := h_4
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_81)
    have h_81 : Litex.In _value_i2 (Litex.R (M := M)) := h_81
    intro h_1
    have h_1 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s) := h_1
    have _formed_body := _value_i2
    exact h_81)
  have _return_1 : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)) → ((M.mem (M.negValue _raw_i2) (M.standard Litex.StandardSetValue.real))) := (by
    intro _raw_i2 h_4 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4)
    have h_4 : Litex.In _value_i2 (Litex.R (M := M)) := h_4
    have h_117 := h_4
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_117)
    have h_117 : Litex.In _value_i2 (Litex.R (M := M)) := h_117
    intro h_2
    have h_2 : (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s) := h_2
    have _formed_body := (Litex.neg _value_i2 (M.real_subset_complex _ h_117))
    exact (by
      let _atomic_wd_1_0 := (Litex.neg _value_i2 (M.real_subset_complex _ h_117))
      exact (Litex.negInR _value_i2 h_117)))
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

theorem h_156 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.piecewiseFnInFnSet (_object_i1 (M := M)))
      )
  )

theorem h_158 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_81 : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) (h_1 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i2) = M.number (_s : ℂ) ∧ _r ≤ _s)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i2)) = (Litex.denote _value_i2)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_81 h_1
          have _case_domain : M.mem (Litex.denote _value_i2) ((_object_i1 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) (Litex.denote _value_i2)).mpr ⟨h_81, (Eq.mpr rfl (True.intro : (fun (_raw_i2 : M.Value) => True) (Litex.denote _value_i2)))⟩
          exact (Litex.piecewiseFn_call_eq (_object_i1 (M := M)) (⟨(fun (_input : M.Value) => (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s)) _input), (fun (_input : M.Value) => (fun (_raw_i2 : M.Value) => _raw_i2) _input)⟩ : Litex.FunctionBranch M) (List.mem_cons_self) (Litex.denote _value_i2) _case_domain (Eq.mpr rfl (h_1 : (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote _value_i2)))).trans rfl)
      )
  )

theorem h_160 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_117 : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) (h_2 : (∃ (_r _s : ℝ), (Litex.denote _value_i2) = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i2)) = (M.negValue (Litex.denote _value_i2))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_117 h_2
          have _case_domain : M.mem (Litex.denote _value_i2) ((_object_i1 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) (Litex.denote _value_i2)).mpr ⟨h_117, (Eq.mpr rfl (True.intro : (fun (_raw_i2 : M.Value) => True) (Litex.denote _value_i2)))⟩
          exact (Litex.piecewiseFn_call_eq (_object_i1 (M := M)) (⟨(fun (_input : M.Value) => (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)) _input), (fun (_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.negValue _raw_i2)) _input)⟩ : Litex.FunctionBranch M) (List.mem_cons_of_mem _ (List.mem_cons_self)) (Litex.denote _value_i2) _case_domain (Eq.mpr rfl (h_2 : (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote _value_i2)))).trans rfl)
      )
  )

noncomputable def _object_w13 := (let _object_w10 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w10 (h_156 (M := M)) (by
  let _atomic_wd_1_0 := _object_w10
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w10).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) True.intro))

theorem h_161 : (by
  let _equal_wd_1_0 := (_object_w13 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w13 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (by
          let _checked_call := _equal_wd_1_0
          let _case_arg_0 := (_equal_wd_1_0).val.argument
          have _case_requirement_0 : (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.argument
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) := (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.argument
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_0).val.argument).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num))))
          have _checked_case_guard : (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.argument
            exact Litex.Lt _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) := (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.argument
            exact ((Litex.NativeBridge.lt_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) = (-2 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
          have _selected_beta := (h_160 (M := M)) _case_arg_0 _case_requirement_0 _checked_case_guard
          exact _selected_beta.trans (let _equal_wd_2_0 := (let _wd_1_0 := (_equal_wd_1_0).val.argument;
          (Litex.neg _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (-2 : ℂ)))) (Litex.numberInC (M := M) (-2 : ℂ))))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (2 : ℂ)) (- (- (2 : ℂ))) (2 : ℂ) (Litex.NativeBridge.denoteNeg (_equal_wd_2_0).val.arg (_equal_wd_2_0).wd _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_2_0).val.arg).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)))))))
      )
  )

noncomputable def _object_w15 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_156 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro)

theorem h_228 : (by
  let _equal_wd_1_0 := (_object_w15 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w15 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (by
          let _checked_call := _equal_wd_1_0
          let _case_arg_0 := (Litex.number (M := M) (3 : ℂ))
          have _case_requirement_0 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
          have _checked_case_guard : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) := ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
          have _selected_beta := (h_158 (M := M)) _case_arg_0 _case_requirement_0 _checked_case_guard
          exact _selected_beta.trans (show @Eq M.Value _ _ from Eq.refl _))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_piecewise_x5f_absolute_x5f_value_x2f_statement_x2e_lit
