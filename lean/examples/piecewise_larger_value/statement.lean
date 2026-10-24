import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_piecewise_x5f_larger_x5f_value_x2f_statement_x2e_lit

universe u v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (show Litex.Obj (M := M) (Litex.PiecewiseFn M) from by
  let _signature := ((show Litex.Obj (M := M) (Litex.FunctionSignature M) from (by
    have _checked_header : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _raw_i2 _raw_i3) → True := by
      intro _raw_i2 _raw_i3 h_3 h_4 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3)
      have h_3 : Litex.In _value_i2 (Litex.R (M := M)) := h_3
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4)
      have h_4 : Litex.In _value_i3 (Litex.R (M := M)) := h_4
      exact True.intro
    exact Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True))))).val
  let _branch_0 := (⟨(fun (_input : M.Value) => (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) _input (M.number (2 : ℂ))) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) _input (M.number (1 : ℂ))) = M.number (_s : ℂ) ∧ _r ≤ _s)), (fun (_input : M.Value) => (Litex.FunctionSemantics.callValue (M := M) _input (M.number (1 : ℂ))))⟩ : Litex.FunctionBranch M)
  let _branch_1 := (⟨(fun (_input : M.Value) => (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) _input (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) _input (M.number (2 : ℂ))) = M.number (_s : ℂ) ∧ _r < _s)), (fun (_input : M.Value) => (Litex.FunctionSemantics.callValue (M := M) _input (M.number (2 : ℂ))))⟩ : Litex.FunctionBranch M)
  have _coverage : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _raw_i2 _raw_i3) → (((∃ (_r _s : ℝ), _raw_i3 = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s)) ∨ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s))) := (by
    intro _raw_i2 _raw_i3 h_5 h_6 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
    have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6)
    have h_6 : Litex.In _value_i3 (Litex.R (M := M)) := h_6
    exact (by
      have _split_member_0 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
      have _split_member_1 : Litex.In _value_i3 (Litex.R (M := M)) := h_6
      rcases lt_or_ge (Litex.NativeBridge.asReal _value_i2 _split_member_0) (Litex.NativeBridge.asReal _value_i3 _split_member_1) with _lt | _ge
      · exact Or.inr ((Litex.NativeBridge.lt_iff_asReal _value_i2 _value_i3 _split_member_0 _split_member_1).mpr _lt)
      · exact Or.inl ((Litex.NativeBridge.le_iff_asReal _value_i3 _value_i2 _split_member_1 _split_member_0).mpr _ge)))
  have _apart_0_1 : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _raw_i2 _raw_i3) → ((∃ (_r _s : ℝ), _raw_i3 = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s)) → ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) → False := (by
    intro _raw_i2 _raw_i3 h_5 h_6 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
    have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6)
    have h_6 : Litex.In _value_i3 (Litex.R (M := M)) := h_6
    have h_44 := h_5
    have h_45 := h_6
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_44)
    have h_44 : Litex.In _value_i2 (Litex.R (M := M)) := h_44
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_45)
    have h_45 : Litex.In _value_i3 (Litex.R (M := M)) := h_45
    intro h_1 _other
    have h_1 : (∃ (_r _s : ℝ), _raw_i3 = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s) := h_1
    have _excluded : ¬ Litex.Lt _value_i2 _value_i3 := (by
      let _left := _value_i3
      let _right := _value_i2
      have _leftReal : Litex.In _left Litex.R := h_45
      have _rightReal : Litex.In _right Litex.R := h_44
      exact fun _opposite => not_lt_of_ge ((Litex.NativeBridge.le_iff_asReal _left _right _leftReal _rightReal).mp h_1) ((Litex.NativeBridge.lt_iff_asReal _right _left _rightReal _leftReal).mp _opposite))
    exact (_excluded _other))
  have _return_0 : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _raw_i2 _raw_i3) → ((∃ (_r _s : ℝ), _raw_i3 = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s)) → ((M.mem _raw_i2 (M.standard Litex.StandardSetValue.real))) := (by
    intro _raw_i2 _raw_i3 h_5 h_6 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
    have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6)
    have h_6 : Litex.In _value_i3 (Litex.R (M := M)) := h_6
    have h_114 := h_5
    have h_115 := h_6
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_114)
    have h_114 : Litex.In _value_i2 (Litex.R (M := M)) := h_114
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_115)
    have h_115 : Litex.In _value_i3 (Litex.R (M := M)) := h_115
    intro h_1
    have h_1 : (∃ (_r _s : ℝ), _raw_i3 = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s) := h_1
    have _formed_body := _value_i2
    exact h_114)
  have _return_1 : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _raw_i2 _raw_i3) → ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) → ((M.mem _raw_i3 (M.standard Litex.StandardSetValue.real))) := (by
    intro _raw_i2 _raw_i3 h_5 h_6 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
    have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6)
    have h_6 : Litex.In _value_i3 (Litex.R (M := M)) := h_6
    have h_161 := h_5
    have h_162 := h_6
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_161)
    have h_161 : Litex.In _value_i2 (Litex.R (M := M)) := h_161
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_162)
    have h_162 : Litex.In _value_i3 (Litex.R (M := M)) := h_162
    intro h_2
    have h_2 : (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s) := h_2
    have _formed_body := _value_i3
    exact h_162)
  apply Litex.piecewiseFn _signature [_branch_0, _branch_1]
  refine ⟨?_, ?_, ?_⟩
  · intro _input _input_member
    obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
      have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
      have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _input).mp _input_member
    rcases _coverage (Litex.FunctionSemantics.callValue (M := M) _input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _input (M.number (2 : ℂ))) (by have _coordinate := Litex.FiniteFunction.coordinate_mem _members (0 : Fin 2); norm_num [Litex.FiniteFunction.index] at _coordinate; exact _coordinate) (by have _coordinate := Litex.FiniteFunction.coordinate_mem _members (1 : Fin 2); norm_num [Litex.FiniteFunction.index] at _coordinate; exact _coordinate) _domain with _case | _case
    · exact ⟨_branch_0, (List.mem_cons_self), _case⟩
    · exact ⟨_branch_1, (List.mem_cons_of_mem _ (List.mem_cons_self)), _case⟩
  · exact (List.Pairwise.cons (by
    intro _branch _member
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
      have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
      have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _input).mp _input_member
      rintro ⟨_left, _right⟩
      exact _apart_0_1 (Litex.FunctionSemantics.callValue (M := M) _input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _input (M.number (2 : ℂ))) (by have _coordinate := Litex.FiniteFunction.coordinate_mem _members (0 : Fin 2); norm_num [Litex.FiniteFunction.index] at _coordinate; exact _coordinate) (by have _coordinate := Litex.FiniteFunction.coordinate_mem _members (1 : Fin 2); norm_num [Litex.FiniteFunction.index] at _coordinate; exact _coordinate) _domain _left _right)
    cases _member) (List.Pairwise.cons (by
    intro _branch _member
    cases _member) List.Pairwise.nil))
  · exact (by
    intro _branch _member
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member _case
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
      have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
      have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _input).mp _input_member
      exact _return_0 (Litex.FunctionSemantics.callValue (M := M) _input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _input (M.number (2 : ℂ))) (by have _coordinate := Litex.FiniteFunction.coordinate_mem _members (0 : Fin 2); norm_num [Litex.FiniteFunction.index] at _coordinate; exact _coordinate) (by have _coordinate := Litex.FiniteFunction.coordinate_mem _members (1 : Fin 2); norm_num [Litex.FiniteFunction.index] at _coordinate; exact _coordinate) _domain _case)
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member _case
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
      have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
      have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _input).mp _input_member
      exact _return_1 (Litex.FunctionSemantics.callValue (M := M) _input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _input (M.number (2 : ℂ))) (by have _coordinate := Litex.FiniteFunction.coordinate_mem _members (0 : Fin 2); norm_num [Litex.FiniteFunction.index] at _coordinate; exact _coordinate) (by have _coordinate := Litex.FiniteFunction.coordinate_mem _members (1 : Fin 2); norm_num [Litex.FiniteFunction.index] at _coordinate; exact _coordinate) _domain _case)
    cases _member))

theorem h_181 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.piecewiseFnInFnSet (_object_i1 (M := M)))
      )
  )

theorem h_183 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_114 : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_115 : M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) (h_1 : (∃ (_r _s : ℝ), (Litex.denote _value_i3) = M.number (_r : ℂ) ∧ (Litex.denote _value_i2) = M.number (_s : ℂ) ∧ _r ≤ _s)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i2), (Litex.denote _value_i3)])) = (Litex.denote _value_i2)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_114 _Host_i3 _rep_i3 _value_i3 h_115 h_1
          have _case_domain : M.mem (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) ((_object_i1 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i2), (Litex.denote _value_i3)])).mpr ⟨(Litex.FiniteFunction.tuple_inCart ![(Litex.denote _value_i2), (Litex.denote _value_i3)] ![M.standard Litex.StandardSetValue.real, M.standard Litex.StandardSetValue.real] (by
            have _finiteProof_0 := (h_114)
            have _finiteProof_1 := (h_115)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )), (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) (M.number (1 : ℂ)) = (Litex.denote _value_i2) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i2), (Litex.denote _value_i3)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) (M.number (2 : ℂ)) = (Litex.denote _value_i3) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i2), (Litex.denote _value_i3)] (1 : Fin 2))) (True.intro : (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.denote _value_i2) (Litex.denote _value_i3)))⟩
          exact (Litex.piecewiseFn_call_eq (_object_i1 (M := M)) (⟨(fun (_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), _raw_i3 = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.FunctionSemantics.callValue (M := M) _input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _input (M.number (2 : ℂ)))), (fun (_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => _raw_i2) (Litex.FunctionSemantics.callValue (M := M) _input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _input (M.number (2 : ℂ))))⟩ : Litex.FunctionBranch M) (List.mem_cons_self) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) _case_domain (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), _raw_i3 = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) (M.number (1 : ℂ)) = (Litex.denote _value_i2) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i2), (Litex.denote _value_i3)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) (M.number (2 : ℂ)) = (Litex.denote _value_i3) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i2), (Litex.denote _value_i3)] (1 : Fin 2))) (h_1 : (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), _raw_i3 = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote _value_i2) (Litex.denote _value_i3)))).trans (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => _raw_i2) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) (M.number (1 : ℂ)) = (Litex.denote _value_i2) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i2), (Litex.denote _value_i3)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) (M.number (2 : ℂ)) = (Litex.denote _value_i3) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i2), (Litex.denote _value_i3)] (1 : Fin 2))))
      )
  )

theorem h_185 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_161 : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_162 : M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)) (h_2 : (∃ (_r _s : ℝ), (Litex.denote _value_i2) = M.number (_r : ℂ) ∧ (Litex.denote _value_i3) = M.number (_s : ℂ) ∧ _r < _s)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i2), (Litex.denote _value_i3)])) = (Litex.denote _value_i3)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_161 _Host_i3 _rep_i3 _value_i3 h_162 h_2
          have _case_domain : M.mem (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) ((_object_i1 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i2), (Litex.denote _value_i3)])).mpr ⟨(Litex.FiniteFunction.tuple_inCart ![(Litex.denote _value_i2), (Litex.denote _value_i3)] ![M.standard Litex.StandardSetValue.real, M.standard Litex.StandardSetValue.real] (by
            have _finiteProof_0 := (h_161)
            have _finiteProof_1 := (h_162)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )), (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) (M.number (1 : ℂ)) = (Litex.denote _value_i2) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i2), (Litex.denote _value_i3)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) (M.number (2 : ℂ)) = (Litex.denote _value_i3) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i2), (Litex.denote _value_i3)] (1 : Fin 2))) (True.intro : (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.denote _value_i2) (Litex.denote _value_i3)))⟩
          exact (Litex.piecewiseFn_call_eq (_object_i1 (M := M)) (⟨(fun (_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.FunctionSemantics.callValue (M := M) _input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _input (M.number (2 : ℂ)))), (fun (_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => _raw_i3) (Litex.FunctionSemantics.callValue (M := M) _input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _input (M.number (2 : ℂ))))⟩ : Litex.FunctionBranch M) (List.mem_cons_of_mem _ (List.mem_cons_self)) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) _case_domain (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) (M.number (1 : ℂ)) = (Litex.denote _value_i2) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i2), (Litex.denote _value_i3)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) (M.number (2 : ℂ)) = (Litex.denote _value_i3) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i2), (Litex.denote _value_i3)] (1 : Fin 2))) (h_2 : (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote _value_i2) (Litex.denote _value_i3)))).trans (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => _raw_i3) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) (M.number (1 : ℂ)) = (Litex.denote _value_i2) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i2), (Litex.denote _value_i3)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i2), (Litex.denote _value_i3)]) (M.number (2 : ℂ)) = (Litex.denote _value_i3) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i2), (Litex.denote _value_i3)] (1 : Fin 2))))
      )
  )

noncomputable def _object_w10 := (let _object_w7 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
(Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) _object_w7 _wd_1_1 (h_181 (M := M)) (by
  let _atomic_wd_1_0 := _object_w7
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w7).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro))

theorem h_186 : (by
  let _equal_wd_1_0 := (_object_w10 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w10 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (by
          let _checked_call := _equal_wd_1_0
          let _case_arg_0 := (_equal_wd_1_0).val.first
          let _case_arg_1 := (Litex.number (M := M) (3 : ℂ))
          have _case_requirement_0 : (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.first
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) := (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.first
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_0).val.first).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num))))
          have _case_requirement_1 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
          have _checked_case_guard : (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.first
            exact Litex.Lt _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) := (by
            let _atomic_wd_1_0 := (_equal_wd_1_0).val.first
            exact ((Litex.NativeBridge.lt_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) = (-2 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
          have _selected_beta := (h_185 (M := M)) _case_arg_0 _case_requirement_0 _case_arg_1 _case_requirement_1 _checked_case_guard
          exact _selected_beta.trans (show @Eq M.Value _ _ from Eq.refl _))))
      )
  )

noncomputable def _object_w12 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_181 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro)

theorem h_253 : (by
  let _equal_wd_1_0 := (_object_w12 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w12 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from (by
          let _checked_call := _equal_wd_1_0
          let _case_arg_0 := (Litex.number (M := M) (5 : ℂ))
          let _case_arg_1 := (Litex.number (M := M) (3 : ℂ))
          have _case_requirement_0 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))
          have _case_requirement_1 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
          have _checked_case_guard : Litex.Le (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) := ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
          have _selected_beta := (h_183 (M := M)) _case_arg_0 _case_requirement_0 _case_arg_1 _case_requirement_1 _checked_case_guard
          exact _selected_beta.trans (show @Eq M.Value _ _ from Eq.refl _))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_piecewise_x5f_larger_x5f_value_x2f_statement_x2e_lit
