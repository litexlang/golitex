import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_two_x5f_argument_x5f_shifted_x5f_quotient_x2f_statement_x2e_lit

universe u v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_53 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_54 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

def prop_2 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) : Prop :=
  ∃ (h_56 : Litex.In _value_i3 (Litex.R (M := M))), ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))

noncomputable def _object_i5 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_predicate_witness : (M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7) (M.standard Litex.StandardSetValue.real))), (¬ ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7) = (M.number (0 : ℂ)))))) (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.divValue _raw_i6 (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7))) (by
  intro _raw_i6 _raw_i7 h_262 h_263 h_57
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_262)
  have h_262 : Litex.In _value_i6 (Litex.R (M := M)) := h_262
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_263)
  have h_263 : Litex.In _value_i7 (Litex.R (M := M)) := h_263
  have h_57 : ((prop_2 (M := M)) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_53 (M := M)) h_263 True.intro)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_predicate_witness : (M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7) (M.standard Litex.StandardSetValue.real))), (¬ ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7) = (M.number (0 : ℂ)))))
            exact h_57)
        )
    )
  have h_271 :=
    (Classical.choose (show ((prop_2 (M := M)) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_53 (M := M)) h_263 True.intro)) from h_57))
  have h_272 :=
    (Classical.choose_spec (show ((prop_2 (M := M)) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_53 (M := M)) h_263 True.intro)) from h_57))
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := _value_i6;
    let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_53 (M := M)) h_263 True.intro);
    (Litex.div _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_262) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (M.real_subset_complex _ h_271)) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact h_272)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := _value_i6;
    let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_53 (M := M)) h_263 True.intro);
    (Litex.div _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_262) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (M.real_subset_complex _ h_271)) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact h_272)))
    exact (Litex.divInR _value_i6 (_atomic_wd_1_0).val.right h_262 h_271 (_atomic_wd_1_0).wd.2.2))))
theorem h_400 : Litex.In (_object_i5 (M := M)) (Litex.fnSet ((_object_i5 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i5 (M := M)))
      )
  )
theorem h_401 : Litex.Same (_object_i5 (M := M)) (_object_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i5 (M := M)))
      )
  )

noncomputable def _object_w16 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)

theorem h_402 : (by
  let _atomic_wd_1_0 := (_object_w16 (M := M))
  exact ((prop_2 (M := M)) _atomic_wd_1_0)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w16 (M := M))
          exact (by
            change (fun (_unfold_arg0 : M.Value) => (∃ (_predicate_witness : (M.mem _unfold_arg0 (M.standard Litex.StandardSetValue.real))), (¬ (_unfold_arg0 = (M.number (0 : ℂ)))))) (Litex.denote _atomic_wd_1_0)
            have _unfold_child : (fun (_unfold_arg0 : M.Value) => (∃ (_predicate_witness : (M.mem _unfold_arg0 (M.standard Litex.StandardSetValue.real))), (¬ (_unfold_arg0 = (M.number (0 : ℂ)))))) (Litex.denote (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))) := (by
            let _atomic_wd_2_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
            exact (Exists.intro (by
              let _atomic_wd_3_0 := _atomic_wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((1 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) + (1 : ℂ)) (2 : ℝ) (by norm_num)))) (by
              let _atomic_wd_3_0 := _atomic_wd_2_0
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_3_0 (Litex.number (M := M) (0 : ℂ)) ((1 : ℂ) + (1 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))
            exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) => (∃ (_predicate_witness : (M.mem _unfold_arg0 (M.standard Litex.StandardSetValue.real))), (¬ (_unfold_arg0 = (M.number (0 : ℂ)))))) (Litex.denote (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) => (∃ (_predicate_witness : (M.mem _unfold_arg0 (M.standard Litex.StandardSetValue.real))), (¬ (_unfold_arg0 = (M.number (0 : ℂ)))))) _unfold_value) ((let _equal_wd_1_0 := _atomic_wd_1_0;
          let _equal_wd_1_1 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ))) = (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) from by
            have _litex_residual : (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) = (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ))) = (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) from by
            let _litex_original := _equal_wd_1_0
            let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro))
            have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
            have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) from rfl))
          ))).trans _litex_residual)))).symm)) _unfold_child
          ))
      )
  )

theorem h_631 : Litex.In (_object_w16 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_402 (M := M)) with ⟨h_56, h_55⟩; exact h_56)
      )
  )

theorem h_632 : ¬ Litex.Same (_object_w16 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_402 (M := M)) with ⟨h_56, h_55⟩; exact h_55)
      )
  )

noncomputable def _object_w19 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_predicate_witness : (M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7) (M.standard Litex.StandardSetValue.real))), (¬ ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7) = (M.number (0 : ℂ)))))) (_object_i5 (M := M)) (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (h_400 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (by
  let _atomic_wd_1_0 := (_object_w16 (M := M))
  exact (h_402 (M := M))))

theorem h_633 : (by
  let _equal_wd_1_0 := (_object_w19 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w19 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (1 : ℂ))])) = (M.number (3 : ℂ)) from by
          have _litex_residual : (M.divValue (M.number (6 : ℂ)) (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ)))) = (M.number (3 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (6 : ℂ));
          let _wd_1_1 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (6 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (1 : ℂ)) = (2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((1 : ℂ) + (1 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((6 : ℂ) / ((1 : ℂ) + (1 : ℂ))) (3 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (6 : ℂ)) (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_2_0).val.right).wd.1 ((_equal_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
          exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (1 : ℂ))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (1 : ℂ))])) = (M.divValue (M.number (6 : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ)))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_predicate_witness : (M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7) (M.standard Litex.StandardSetValue.real))), (¬ ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7) = (M.number (0 : ℂ)))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (by
            let _atomic_wd_1_0 := (_object_w16 (M := M))
            exact (h_402 (M := M)))))
          have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_401 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
          have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_predicate_witness : (M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7) (M.standard Litex.StandardSetValue.real))), (¬ ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7) = (M.number (0 : ℂ)))))) (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.divValue _raw_i6 (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7))) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (∃ (_predicate_witness : (M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7) (M.standard Litex.StandardSetValue.real))), (¬ ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7) = (M.number (0 : ℂ)))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.divValue _raw_i6 (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7))) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.divValue _raw_i6 (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7))) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.divValue (M.number (6 : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ)))) from rfl))
        ))).trans (congrArg₂ M.divValue rfl (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ))) = (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) from by
          let _litex_original := (_object_w16 (M := M))
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (1 : ℂ)) (M.number (1 : ℂ))) from rfl))
        )))).trans _litex_residual)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_two_x5f_argument_x5f_shifted_x5f_quotient_x2f_statement_x2e_lit
