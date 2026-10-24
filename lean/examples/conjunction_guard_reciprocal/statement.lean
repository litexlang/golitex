import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_conjunction_x5f_guard_x5f_reciprocal_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

def prop_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) : Prop :=
  ∃ (h_4 : Litex.In _value_i1 (Litex.R (M := M))), ((¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) ∧ (Litex.Same _value_i1 _value_i1))

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (((¬ (_raw_i4 = (M.number (0 : ℂ))))) ∧ ((_raw_i4 = _raw_i4))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
  intro _raw_i4 h_35 h_5
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_35)
  have h_35 : Litex.In _value_i4 (Litex.R (M := M)) := h_35
  have h_5 : ((prop_1 (M := M)) _value_i4) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (((¬ (_raw_i4 = (M.number (0 : ℂ))))) ∧ ((_raw_i4 = _raw_i4))))
            exact h_5)
        )
    )
  have h_36 :=
    (Classical.choose (show ((prop_1 (M := M)) _value_i4) from h_5))
  have h_39 : ((¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))) ∧ (Litex.Same _value_i4 _value_i4)) :=
    (by
      litex_checked_step =>
        exact (
          (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3)
        )
    )
  have h_37 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (And.left (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3))
        )
    )
  have h_38 : Litex.Same _value_i4 _value_i4 :=
    (by
      litex_checked_step =>
        exact (
          (And.right (by rcases h_5 with ⟨h_4, h_3⟩; exact h_3))
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_35) h_37)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_35) h_37)
    exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_35 (_atomic_wd_1_0).wd.2.2))))
theorem h_113 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_114 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

theorem h_115 : ((prop_1 (M := M)) (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (Exists.intro (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (And.intro (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (show @Eq M.Value _ _ from Eq.refl _)))
      )
  )

theorem h_123 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_115 (M := M)) with ⟨h_4, h_3⟩; exact h_4)
      )
  )

theorem h_126 : ((¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ))) ∧ (Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_115 (M := M)) with ⟨h_4, h_3⟩; exact h_3)
      )
  )

theorem h_124 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (And.left (by rcases (h_115 (M := M)) with ⟨h_4, h_3⟩; exact h_3))
      )
  )

theorem h_125 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (And.right (by rcases (h_115 (M := M)) with ⟨h_4, h_3⟩; exact h_3))
      )
  )

noncomputable def _object_w9 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (((¬ (_raw_i4 = (M.number (0 : ℂ))))) ∧ ((_raw_i4 = _raw_i4))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_113 (M := M)) (h_123 (M := M)) (h_115 (M := M)))

noncomputable def _object_w10 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (h_124 (M := M)))

theorem h_127 : (by
  let _equal_wd_1_0 := (_object_w9 (M := M))
  let _equal_wd_1_1 := (_object_w10 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w9 (M := M));
        let _equal_wd_1_1 := (_object_w10 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (2 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) from by
          have _litex_residual : (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (2 : ℂ))))).trans (by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (((¬ (_raw_i4 = (M.number (0 : ℂ))))) ∧ ((_raw_i4 = _raw_i4))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (h_123 (M := M)) (h_115 (M := M))))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_114 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (((¬ (_raw_i4 = (M.number (0 : ℂ))))) ∧ ((_raw_i4 = _raw_i4))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (((¬ (_raw_i4 = (M.number (0 : ℂ))))) ∧ ((_raw_i4 = _raw_i4))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_conjunction_x5f_guard_x5f_reciprocal_x2f_statement_x2e_lit
