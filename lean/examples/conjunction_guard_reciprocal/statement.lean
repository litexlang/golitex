import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_conjunction_x5f_guard_x5f_reciprocal_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

def prop_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) : Prop :=
  ∃ (h_4 : Litex.In _value_i1 (Litex.R (M := M))), (¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) ∧ Litex.Same _value_i1 _value_i1)

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
  intro _raw_i4 h_35 h_5
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_35)
  have h_35 : Litex.In _value_i4 (Litex.R (M := M)) := h_35
  have h_5 : ((prop_1 (M := M)) _value_i4) :=
    (by
      change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))
      exact h_5)
  have h_36 : Litex.In _value_i4 (Litex.R (M := M)) :=
    (by rcases h_5 with ⟨h_4, h_3⟩; exact h_4)
  have h_41 : (¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) ∧ Litex.Same _value_i4 _value_i4) :=
    (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3)
  have h_39 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
    (And.left (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3))
  have h_40 : Litex.Same _value_i4 _value_i4 :=
    (And.right (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3))
  change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_35) h_39) (Litex.R (M := M))
  exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_35 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_35) h_39)).wd.2.2)))
theorem h_117 : Litex.In (_object_i3 (M := M)) (by
  have _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))) _raw_i4) → True := by
    intro _raw_i4 h_110 h_5
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_110)
    have h_110 : Litex.In _value_i4 (Litex.R (M := M)) := h_110
    have h_5 : ((prop_1 (M := M)) _value_i4) :=
      (by
        change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))
        exact h_5)
    have h_111 : Litex.In _value_i4 (Litex.R (M := M)) :=
      (by rcases h_5 with ⟨h_4, h_3⟩; exact h_4)
    have h_116 : (¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) ∧ Litex.Same _value_i4 _value_i4) :=
      (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3)
    have h_114 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
      (And.left (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3))
    have h_115 : Litex.Same _value_i4 _value_i4 :=
      (And.right (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3))
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))))) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_118 : Litex.Same (_object_i3 (M := M)) (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
  intro _raw_i4 h_35 h_5
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_35)
  have h_35 : Litex.In _value_i4 (Litex.R (M := M)) := h_35
  have h_5 : ((prop_1 (M := M)) _value_i4) :=
    (by
      change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))
      exact h_5)
  have h_36 : Litex.In _value_i4 (Litex.R (M := M)) :=
    (by rcases h_5 with ⟨h_4, h_3⟩; exact h_4)
  have h_41 : (¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) ∧ Litex.Same _value_i4 _value_i4) :=
    (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3)
  have h_39 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
    (And.left (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3))
  have h_40 : Litex.Same _value_i4 _value_i4 :=
    (And.right (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3))
  change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_35) h_39) (Litex.R (M := M))
  exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_35 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_35) h_39)).wd.2.2))) :=
  (Litex.sameRefl (_object_i3 (M := M)))

theorem h_119 : ((prop_1 (M := M)) (Litex.number (M := M) (2 : ℂ))) :=
  (Exists.intro (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num))) (And.intro (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))))

theorem h_127 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
  (by rcases (h_119 (M := M)) with ⟨h_4, h_3⟩; exact h_4)

theorem h_131 : (¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ∧ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ))) :=
  (by rcases (h_119 (M := M)) with ⟨h_4, h_3⟩; exact h_3)

theorem h_129 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
  (And.left (by rcases (h_119 (M := M)) with ⟨h_4, h_3⟩; exact h_3))

theorem h_130 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
  (And.right (by rcases (h_119 (M := M)) with ⟨h_4, h_3⟩; exact h_3))

theorem h_132 : Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_117 (M := M)) (h_127 (M := M)) (h_119 (M := M))) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (h_129 (M := M))) :=
  (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (2 : ℂ))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_117 (M := M)) (h_127 (M := M)) (h_119 (M := M)))
    let _litex_literal := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))) (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
      intro _raw_i4 h_35 h_5
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_35)
      have h_35 : Litex.In _value_i4 (Litex.R (M := M)) := h_35
      have h_5 : ((prop_1 (M := M)) _value_i4) :=
        (by
          change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))
          exact h_5)
      have h_36 : Litex.In _value_i4 (Litex.R (M := M)) :=
        (by rcases h_5 with ⟨h_4, h_3⟩; exact h_4)
      have h_41 : (¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) ∧ Litex.Same _value_i4 _value_i4) :=
        (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3)
      have h_39 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (And.left (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3))
      have h_40 : Litex.Same _value_i4 _value_i4 :=
        (And.right (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3))
      change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_35) h_39) (Litex.R (M := M))
      exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_35 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_35) h_39)).wd.2.2))) (Litex.number (M := M) (2 : ℂ)) (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
      intro _raw_i4 h_35 h_5
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_35)
      have h_35 : Litex.In _value_i4 (Litex.R (M := M)) := h_35
      have h_5 : ((prop_1 (M := M)) _value_i4) :=
        (by
          change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))
          exact h_5)
      have h_36 : Litex.In _value_i4 (Litex.R (M := M)) :=
        (by rcases h_5 with ⟨h_4, h_3⟩; exact h_4)
      have h_41 : (¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) ∧ Litex.Same _value_i4 _value_i4) :=
        (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3)
      have h_39 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (And.left (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3))
      have h_40 : Litex.Same _value_i4 _value_i4 :=
        (And.right (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3))
      change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_35) h_39) (Litex.R (M := M))
      exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_35 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_35) h_39)).wd.2.2)))) (h_127 (M := M)) (h_119 (M := M)))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (((Litex.sameRefl (_object_i3 (M := M)))).trans (h_118 (M := M))) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), ((¬ (_raw_i4 = (M.number (0 : ℂ)))) ∧ (_raw_i4 = _raw_i4)))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) from rfl))
  ))).trans (Litex.sameRefl (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (h_129 (M := M)))))
end LitexCompiled.file_lean_x2f_examples_x2f_conjunction_x5f_guard_x5f_reciprocal_x2f_statement_x2e_lit
