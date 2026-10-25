import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_piecewise_x5f_inverse_x5f_magnitude_x2f_statement_x2e_lit

universe u v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (show Litex.Obj (M := M) (Litex.PiecewiseFn M) from by
  let _signature := ((show Litex.Obj (M := M) (Litex.FunctionSignature M) from (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
      intro _raw_i2 h_4 h_1
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4)
      have h_4 : Litex.In _value_i2 (Litex.R (M := M)) := h_4
      have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i2 = (M.number (0 : ℂ))))
                exact h_1)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))))).val
  let _branch_0 := (⟨(fun (_input : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _input = M.number (_s : ℂ) ∧ _r < _s)), (fun (_input : M.Value) => (M.divValue (M.number (1 : ℂ)) _input))⟩ : Litex.FunctionBranch M)
  let _branch_1 := (⟨(fun (_input : M.Value) => (∃ (_r _s : ℝ), _input = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)), (fun (_input : M.Value) => (M.divValue (M.negValue (M.number (1 : ℂ))) _input))⟩ : Litex.FunctionBranch M)
  have _coverage : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)) ∨ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s))) := (by
    intro _raw_i2 h_5 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
    have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) := h_1
    exact (by
      have _split_member_0 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
      have _split_member_1 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
      rcases lt_or_ge (Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) _split_member_1) (Litex.NativeBridge.asReal _value_i2 _split_member_0) with _lt | _ge
      · exact Or.inl ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) _value_i2 _split_member_1 _split_member_0).mpr _lt)
      · exact Or.inr ((Litex.NativeBridge.le_iff_asReal _value_i2 (Litex.number (M := M) (0 : ℂ)) _split_member_0 _split_member_1).mpr _ge)))
  have _apart_0_1 : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)) → ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) → False := (by
    intro _raw_i2 h_5 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
    have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) := h_1
    have h_31 := h_5
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_31)
    have h_31 : Litex.In _value_i2 (Litex.R (M := M)) := h_31
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) := h_1
    intro h_2 _other
    have h_2 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s) := h_2
    have _excluded : ¬ Litex.Le _value_i2 (Litex.number (M := M) (0 : ℂ)) := (by
      let _left := (Litex.number (M := M) (0 : ℂ))
      let _right := _value_i2
      have _leftReal : Litex.In _left Litex.R := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
      have _rightReal : Litex.In _right Litex.R := h_31
      exact fun _opposite => not_le_of_gt ((Litex.NativeBridge.lt_iff_asReal _left _right _leftReal _rightReal).mp h_2) ((Litex.NativeBridge.le_iff_asReal _right _left _rightReal _leftReal).mp _opposite))
    exact (_excluded _other))
  have _return_0 : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)) → ((M.mem (M.divValue (M.number (1 : ℂ)) _raw_i2) (M.standard Litex.StandardSetValue.real))) := (by
    intro _raw_i2 h_5 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
    have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) := h_1
    have h_52 := h_5
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_52)
    have h_52 : Litex.In _value_i2 (Litex.R (M := M)) := h_52
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) := h_1
    intro h_2
    have h_2 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s) := h_2
    have _formed_body := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_52) h_1)
    exact (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_52) h_1)
      exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_52 (_atomic_wd_1_0).wd.2.2)))
  have _return_1 : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) → ((M.mem (M.divValue (M.negValue (M.number (1 : ℂ))) _raw_i2) (M.standard Litex.StandardSetValue.real))) := (by
    intro _raw_i2 h_5 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
    have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) := h_1
    have h_100 := h_5
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_100)
    have h_100 : Litex.In _value_i2 (Litex.R (M := M)) := h_100
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) := h_1
    intro h_3
    have h_3 : (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) := h_3
    have _formed_body := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
    let _wd_1_1 := _value_i2;
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (M.real_subset_complex _ h_100) h_1))
    exact (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
      let _wd_1_1 := _value_i2;
      (Litex.div _wd_1_0 _wd_1_1 (by
        let _atomic_wd_2_0 := _wd_1_0
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (M.real_subset_complex _ h_100) h_1))
      exact (Litex.divInR (_atomic_wd_1_0).val.left _value_i2 (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.left (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))) h_100 (_atomic_wd_1_0).wd.2.2)))
  apply Litex.piecewiseFn _signature [_branch_0, _branch_1]
  refine ⟨?_, ?_, ?_⟩
  · intro _input _input_member
    obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _input).mp _input_member
    rcases _coverage _input _members _domain with _case | _case
    · exact ⟨_branch_0, (List.mem_cons_self), _case⟩
    · exact ⟨_branch_1, (List.mem_cons_of_mem _ (List.mem_cons_self)), _case⟩
  · exact (List.Pairwise.cons (by
    intro _branch _member
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _input).mp _input_member
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
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _input).mp _input_member
      exact _return_0 _input _members _domain _case)
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member _case
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _input).mp _input_member
      exact _return_1 _input _members _domain _case)
    cases _member))

theorem h_186 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.piecewiseFnInFnSet (_object_i1 (M := M)))
      )
  )

theorem h_188 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_52 : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) (h_1 : (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) (h_2 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i2) = M.number (_s : ℂ) ∧ _r < _s)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i2)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_52 h_1 h_2
          have _case_domain : M.mem (Litex.denote _value_i2) ((_object_i1 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) (Litex.denote _value_i2)).mpr ⟨h_52, (Eq.mpr rfl (h_1 : (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (Litex.denote _value_i2)))⟩
          exact (Litex.piecewiseFn_call_eq (_object_i1 (M := M)) (⟨(fun (_input : M.Value) => (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)) _input), (fun (_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _input)⟩ : Litex.FunctionBranch M) (List.mem_cons_self) (Litex.denote _value_i2) _case_domain (Eq.mpr rfl (h_2 : (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote _value_i2)))).trans rfl)
      )
  )

theorem h_190 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_100 : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) (h_1 : (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) (h_3 : (∃ (_r _s : ℝ), (Litex.denote _value_i2) = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i2)) = (M.divValue (M.negValue (M.number (1 : ℂ))) (Litex.denote _value_i2))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_100 h_1 h_3
          have _case_domain : M.mem (Litex.denote _value_i2) ((_object_i1 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) (Litex.denote _value_i2)).mpr ⟨h_100, (Eq.mpr rfl (h_1 : (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (Litex.denote _value_i2)))⟩
          exact (Litex.piecewiseFn_call_eq (_object_i1 (M := M)) (⟨(fun (_input : M.Value) => (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) _input), (fun (_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.divValue (M.negValue (M.number (1 : ℂ))) _raw_i2)) _input)⟩ : Litex.FunctionBranch M) (List.mem_cons_of_mem _ (List.mem_cons_self)) (Litex.denote _value_i2) _case_domain (Eq.mpr rfl (h_3 : (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote _value_i2)))).trans rfl)
      )
  )

noncomputable def _object_w12 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_186 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

noncomputable def _object_w13 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_191 : (by
  let _equal_wd_1_0 := (_object_w12 (M := M))
  let _equal_wd_1_1 := (_object_w13 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w12 (M := M));
        let _equal_wd_1_1 := (_object_w13 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
          let _checked_call := _equal_wd_1_0
          let _case_arg_0 := (Litex.number (M := M) (2 : ℂ))
          have _case_requirement_0 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          have _case_requirement_1 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
          have _checked_case_guard : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) := ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
          have _selected_beta := (h_188 (M := M)) _case_arg_0 _case_requirement_0 _case_requirement_1 _checked_case_guard
          exact _selected_beta.trans (show @Eq M.Value _ _ from Eq.refl _))))
      )
  )

noncomputable def _object_w24 := (let _object_w14 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w14 (h_186 (M := M)) (by
  let _atomic_wd_1_0 := _object_w14
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w14).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (by
  let _atomic_wd_1_0 := _object_w14
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (- (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w14).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))

theorem h_340 : (by
  let _equal_wd_1_0 := (_object_w24 (M := M))
  let _equal_wd_1_1 := (_object_w13 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w24 (M := M));
        let _equal_wd_1_1 := (_object_w13 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
          let _checked_call := _equal_wd_1_0
          let _case_arg_0 := (_equal_wd_1_0).val.argument
          have _case_requirement_0 : (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.argument
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) := (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.argument
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_0).val.argument).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num))))
          have _case_requirement_1 : (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.argument
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) := (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.argument
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (- (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_0).val.argument).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
          have _checked_case_guard : (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.argument
            exact Litex.Le _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) := (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.argument
            exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (by
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
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
          have _selected_beta := (h_190 (M := M)) _case_arg_0 _case_requirement_0 _case_requirement_1 _checked_case_guard
          exact _selected_beta.trans (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (_equal_wd_1_0).val.argument;
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (-2 : ℂ)))) (Litex.numberInC (M := M) (-2 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (- (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
          let _equal_wd_2_1 := (_object_w13 (M := M));
          (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 ((- (1 : ℂ)) / (- (2 : ℂ))) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (_equal_wd_2_0).val.left (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_2_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_2_0).val.right).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num)))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_piecewise_x5f_inverse_x5f_magnitude_x2f_statement_x2e_lit
