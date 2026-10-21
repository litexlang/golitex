import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_numeric_x5f_set_x5f_alias_x5f_functions_x2f_statement_x2e_lit

universe u v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.R (M := M))
theorem h_3 : Litex.IsSet (_object_i1 (M := M)) :=
  (Litex.isSet (Litex.R (M := M)))
theorem h_4 : Litex.Same (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (Litex.sameRefl (Litex.R (M := M)))

noncomputable def _object_i2 := (_object_i1 (M := M))
theorem h_5 : Litex.Same (_object_i2 (M := M)) (_object_i1 (M := M)) :=
  (Litex.sameRefl (_object_i1 (M := M)))

noncomputable def _object_i3 := (Litex.formulaFnOn (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i2 (M := M))) (Litex.isSet (_object_i1 (M := M))) (Litex.isSet (_object_i2 (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => _raw_i4) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (_object_i1 (M := M))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => _raw_i4) _raw_i4) (Litex.denote (_object_i2 (M := M))) := (by
    intro _raw_i4 h_55 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_55)
    have h_55 : Litex.In _value_i4 (_object_i1 (M := M)) := h_55
    change Litex.In _value_i4 (_object_i2 (M := M))
    exact (Litex.inOfSame _value_i4 _value_i4 (_object_i1 (M := M)) (_object_i2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) ((h_5 (M := M))).symm h_55))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i2 (M := M))) (Litex.isSet (_object_i1 (M := M))) (Litex.isSet (_object_i2 (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_62 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_63 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (Litex.sameRefl (_object_i3 (M := M)))

noncomputable def _object_w4 := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
Litex.callOn ((_object_i3 (M := M))).val.signature (_object_i3 (M := M)) _litex_call_arg_0 (h_62 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))), True.intro⟩))

theorem h_64 : Litex.Same (_object_w4 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (2 : ℂ))) = (M.number (2 : ℂ)) from by
    let _litex_original := (_object_w4 (M := M))
    let _litex_formula := (_object_i3 (M := M))
    have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_63 (M := M))
    have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) _litex_original.wd.2
    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => _raw_i4) _litex_input) (Litex.denote _litex_original.val.argument) = (M.number (2 : ℂ)); exact rfl))
  )).trans (show @Eq M.Value _ _ from Eq.refl _))

def prop_5 {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) : Prop :=
  ∃ (h_137 : Litex.In _value_i5 (_object_i1 (M := M))), ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))

noncomputable def _object_i7 := (Litex.formulaFnOn (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote (_object_i1 (M := M))) (Litex.isSet (_object_i2 (M := M))) (Litex.isSet (_object_i1 (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i8)) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote (_object_i2 (M := M))) → ((fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i8)) _raw_i8) (Litex.denote (_object_i1 (M := M))) := (by
    intro _raw_i8 h_204 h_138
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_204)
    have h_204 : Litex.In _value_i8 (_object_i2 (M := M)) := h_204
    have h_138 : ((prop_5 (M := M)) _value_i8) :=
      (by
        change (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))
        exact h_138)
    have h_205 :=
      (Classical.choose (show ((prop_5 (M := M)) _value_i8) from h_138))
    have h_206 :=
      (Classical.choose_spec (show ((prop_5 (M := M)) _value_i8) from h_138))
    change (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (((h_5 (M := M))).trans (h_4 (M := M))) h_204)) h_206)
      exact Litex.In _atomic_wd_1_0 (_object_i1 (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (((h_5 (M := M))).trans (h_4 (M := M))) h_204)) h_206)
      exact (Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.R (M := M)) (_object_i1 (M := M)) (Litex.sameRefl _atomic_wd_1_0) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (by
        let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (((h_5 (M := M))).trans (h_4 (M := M))) h_204)) h_206)
        exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.inOfSame _value_i8 _value_i8 (_object_i2 (M := M)) (Litex.R (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (((h_5 (M := M))).trans (h_4 (M := M))) h_204) (_atomic_wd_2_0).wd.2.2)))))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (_object_i2 (M := M))) (Litex.denote (_object_i1 (M := M))) (Litex.isSet (_object_i2 (M := M))) (Litex.isSet (_object_i1 (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_337 : Litex.In (_object_i7 (M := M)) (Litex.fnSet ((_object_i7 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i7 (M := M)))
theorem h_338 : Litex.Same (_object_i7 (M := M)) (_object_i7 (M := M)) :=
  (Litex.sameRefl (_object_i7 (M := M)))

theorem h_339 : ((prop_5 (M := M)) (Litex.number (M := M) (2 : ℂ))) :=
  (Exists.intro (Litex.inOfSame (_object_w4 (M := M)) (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (_object_i1 (M := M)) ((((Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))).trans ((h_64 (M := M))).symm)).symm (Litex.sameRefl (_object_i1 (M := M))) (by
    let _litex_return_call := (_object_w4 (M := M))
    exact Litex.inOfSame _litex_return_call _litex_return_call (_object_i2 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl _litex_return_call) (h_5 (M := M)) (Litex.callOnInOutput _litex_return_call))) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_362 : Litex.In (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) :=
  (by rcases (h_339 (M := M)) with ⟨h_137, h_136⟩; exact h_137)

theorem h_363 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
  (by rcases (h_339 (M := M)) with ⟨h_137, h_136⟩; exact h_136)

noncomputable def _object_w9 := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
Litex.callOn ((_object_i7 (M := M))).val.signature (_object_i7 (M := M)) _litex_call_arg_0 (h_337 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (_object_i2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) ((h_5 (M := M))).symm (h_362 (M := M))), (h_339 (M := M))⟩))

noncomputable def _object_w10 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (h_363 (M := M)))

theorem h_364 : Litex.Same (_object_w9 (M := M)) (_object_w10 (M := M)) :=
  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (M.number (2 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) from by
    have _litex_residual : (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (M.number (2 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i7 (M := M))) (M.number (2 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) from by
    let _litex_original := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
  Litex.callOn ((_object_i7 (M := M))).val.signature (_object_i7 (M := M)) _litex_call_arg_0 (h_337 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_i1 (M := M)) (_object_i2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) ((h_5 (M := M))).symm (h_362 (M := M))), (h_339 (M := M))⟩))
    let _litex_literal := (let _wd_1_0 := (_object_i7 (M := M));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (let _litex_call_arg_0 := _wd_1_1;
  Litex.callOnDomain (_object_i2 (M := M)) (_object_i1 (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i8 (Litex.denote (_object_i1 (M := M))))), (¬ (_raw_i8 = (M.number (0 : ℂ)))))) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inOfSame _wd_1_1 _wd_1_1 (_object_i1 (M := M)) (_object_i2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) ((h_5 (M := M))).symm (h_362 (M := M))) (h_339 (M := M))))
    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_338 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i8)) _litex_input) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))); exact rfl))
  ))).trans _litex_residual)
end LitexCompiled.file_lean_x2f_examples_x2f_numeric_x5f_set_x5f_alias_x5f_functions_x2f_statement_x2e_lit
