import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_reciprocal_x5f_product_x5f_and_x5f_evaluation_x2f_statement_x2e_lit

universe u v1 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

def prop_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) : Prop :=
  ∃ (h_2 : Litex.In _value_i1 (Litex.R (M := M))), ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
  intro _raw_i4 h_45 h_3
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_45)
  have h_45 : Litex.In _value_i4 (Litex.R (M := M)) := h_45
  have h_3 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      change (¬ (_raw_i4 = (M.number (0 : ℂ))))
      exact h_3)
  change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_45) h_3) (Litex.R (M := M))
  exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_45 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_45) h_3)).wd.2.2)))
theorem h_94 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_95 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (Litex.sameRefl (_object_i3 (M := M)))

theorem h_98 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_102 : Litex.In _value_i6 (Litex.R (M := M))) (h_96 : ((prop_1 (M := M)) _value_i6)), (by
  have h_104 :=
    (Classical.choose_spec (show ((prop_1 (M := M)) _value_i6) from h_96))
  exact Litex.Same (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_102 h_104);
  let _wd_1_1 := _value_i6;
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _wd_1_1 (h_94 (M := M)) h_102 h_104) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _wd_1_1 (h_94 (M := M)) h_102 h_104))) (M.real_subset_complex _ h_102))) (Litex.number (M := M) (1 : ℂ))
) :=
  (by
    intro _Host_i6 _rep_i6 _value_i6 h_102 h_96
    have h_103 :=
      (Classical.choose (show ((prop_1 (M := M)) _value_i6) from h_96))
    have h_104 :=
      (Classical.choose_spec (show ((prop_1 (M := M)) _value_i6) from h_96))
    have h_220 : Litex.In _value_i6 (Litex.R (M := M)) :=
      h_102
    have h_221 :=
      (Classical.choose (show ((prop_1 (M := M)) _value_i6) from h_96))
    have h_222 :=
      (Classical.choose_spec (show ((prop_1 (M := M)) _value_i6) from h_96))
    let _object_w12 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_220 h_222)

    let _object_w13 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_220) h_222)

    have h_99 : Litex.Same _object_w12 _object_w13 :=
      (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
        have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i6)))).trans (by
        let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_220 h_222)
        let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
        let _wd_1_1 := _value_i6;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_220 h_222))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_95 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from rfl))
      ))).trans _litex_residual)
    let _object_w14 := (let _wd_1_0 := _object_w12;
    let _wd_1_1 := _value_i6;
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.realToComplex _object_w12 (Litex.callInOutput _object_w12)) (M.real_subset_complex _ h_220)))

    let _object_w15 := (let _wd_1_0 := _object_w13;
    let _wd_1_1 := _value_i6;
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_220) (_wd_1_0).wd.2.2) (M.real_subset_complex _ h_220)))

    have h_100 : Litex.Same _object_w14 _object_w15 :=
      (congrArg₂ M.mulValue h_99 (show @Eq M.Value _ _ from Eq.refl _))
    have h_101 : Litex.Same _object_w15 (Litex.number (M := M) (1 : ℂ)) :=
      (Litex.NativeBridge.sameOfDenoteNumber _object_w15 (Litex.number (M := M) (1 : ℂ)) (((1 : ℂ) / (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_220))) * (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_220))) (1 : ℂ) (Litex.NativeBridge.denoteMul (_object_w15).val.left _value_i6 (_object_w15).wd.1 (_object_w15).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) _value_i6 (_object_w13).wd.1 (_object_w13).wd.2.1 (_object_w13).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_220))) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_220))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (((div_eq_iff (Litex.NativeBridge.nativeNonzeroOfDenote _value_i6 (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_220)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_220)) ((_object_w15).val.left).wd.2.2)).mp (Litex.NativeBridge.nativeEqOfDenoteNumber (_object_w15).val.left (_object_w15).val.left ((1 : ℂ) / (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_220))) ((1 : ℂ) / (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_220))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) _value_i6 (_object_w13).wd.1 (_object_w13).wd.2.1 (_object_w13).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_220))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) _value_i6 (_object_w13).wd.1 (_object_w13).wd.2.1 (_object_w13).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_220))) (show @Eq M.Value _ _ from Eq.refl _))).symm))
    exact ((h_100).trans h_101)
  )

noncomputable def _object_i8 := (Litex.number (M := M) (2 : ℂ))
theorem h_888 : Litex.In (_object_i8 (M := M)) (Litex.R (M := M)) :=
  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
theorem h_889 : Litex.Same (_object_i8 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))

theorem h_890 : ((prop_1 (M := M)) (_object_i8 (M := M))) :=
  (Exists.intro (h_888 (M := M)) (Litex.notSameOfSame (Litex.number (M := M) (2 : ℂ)) (_object_i8 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((h_889 (M := M))).symm (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_944 : Litex.In (_object_i8 (M := M)) (Litex.R (M := M)) :=
  (by rcases (h_890 (M := M)) with ⟨h_2, h_1⟩; exact h_2)

theorem h_945 : ¬ Litex.Same (_object_i8 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by rcases (h_890 (M := M)) with ⟨h_2, h_1⟩; exact h_1)

noncomputable def _object_i9 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)))
theorem h_958 : Litex.Same (_object_i9 (M := M)) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))) :=
  (Litex.sameRefl (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))))

noncomputable def _object_w22 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (_object_i8 (M := M)) (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_888 (M := M))) (h_945 (M := M)))

theorem h_959 : Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))) (_object_w22 (M := M)) :=
  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote (_object_i8 (M := M)))) = (M.divValue (M.number (1 : ℂ)) (Litex.denote (_object_i8 (M := M)))) from by
    have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote (_object_i8 (M := M)))) = (M.divValue (M.number (1 : ℂ)) (Litex.denote (_object_i8 (M := M)))) := (show @Eq M.Value _ _ from Eq.refl _)
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote (_object_i8 (M := M)))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)))
    let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
    let _wd_1_1 := (_object_i8 (M := M));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (h_888 (M := M)) (h_945 (M := M))))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_95 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote (_object_i8 (M := M)))) from rfl))
  ))).trans _litex_residual)

noncomputable def _object_w23 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame (_object_i8 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_889 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_945 (M := M))))

theorem h_1513 : Litex.Same (_object_w22 (M := M)) (_object_w23 (M := M)) :=
  (congrArg₂ M.divValue (show @Eq M.Value _ _ from Eq.refl _) (h_889 (M := M)))

theorem h_1544 : (by
  have h_1545 : Litex.In (_object_i8 (M := M)) (Litex.R (M := M)) :=
    (h_888 (M := M))
  exact Litex.Same (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)));
  let _wd_1_1 := (_object_i8 (M := M));
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))))) (M.real_subset_complex _ h_1545))) (Litex.number (M := M) (1 : ℂ))
) :=
  (by
    have h_1545 : Litex.In (_object_i8 (M := M)) (Litex.R (M := M)) :=
      (h_888 (M := M))
    have h_1546 : ((prop_1 (M := M)) (_object_i8 (M := M))) :=
      (h_890 (M := M))
    have h_1556 :=
      (Classical.choose (show ((prop_1 (M := M)) (_object_i8 (M := M))) from h_1546))
    have h_1557 :=
      (Classical.choose_spec (show ((prop_1 (M := M)) (_object_i8 (M := M))) from h_1546))
    have h_1547 : Litex.Same (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)));
    let _wd_1_1 := (_object_i8 (M := M));
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))))) (M.real_subset_complex _ h_1545))) (Litex.number (M := M) (1 : ℂ)) :=
      ((h_98 (M := M)) (_object_i8 (M := M)) h_1545 h_1546)
    exact (((Litex.sameRefl (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)));
  let _wd_1_1 := (_object_i8 (M := M));
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))))) (M.real_subset_complex _ h_1545))))).symm.trans ((h_1547).trans (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))))
  )

theorem h_1801 : Litex.Same (_object_i9 (M := M)) (_object_w23 (M := M)) :=
  (((((h_958 (M := M))).trans (h_959 (M := M)))).trans (h_1513 (M := M)))
end LitexCompiled.file_lean_x2f_examples_x2f_reciprocal_x5f_product_x5f_and_x5f_evaluation_x2f_statement_x2e_lit
