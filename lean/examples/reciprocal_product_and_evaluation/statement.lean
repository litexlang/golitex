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
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i4 = (M.number (0 : ℂ))))
            exact h_3)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_45) h_3)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_45) h_3)
    exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_45 (_atomic_wd_1_0).wd.2.2))))
theorem h_94 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_95 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

theorem h_98 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_102 : Litex.In _value_i6 (Litex.R (M := M))) (h_96 : ((prop_1 (M := M)) _value_i6)), (by
  have h_104 :=
    (Classical.choose_spec (show ((prop_1 (M := M)) _value_i6) from h_96))
  exact (by
    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_102 h_104);
    let _wd_1_1 := _value_i6;
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (M.real_subset_complex _ h_102)))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_102 h_96
          have h_103 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i6) from h_96))
          have h_104 :=
            (Classical.choose_spec (show ((prop_1 (M := M)) _value_i6) from h_96))
          have h_220 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_102
                )
            )
          have h_221 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i6) from h_96))
          have h_222 :=
            (Classical.choose_spec (show ((prop_1 (M := M)) _value_i6) from h_96))
          let _object_w14 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_220 h_222)

          let _object_w15 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_220) h_222)

          have h_99 : (by
            let _equal_wd_1_0 := _object_w14
            let _equal_wd_1_1 := _object_w15
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w14;
                  let _equal_wd_1_1 := _object_w15;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
                    have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i6)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
                    let _wd_1_1 := _value_i6;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_220 h_222))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_95 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w16 := (let _wd_1_0 := _object_w14;
          let _wd_1_1 := _value_i6;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w14
            exact (Litex.realToComplex _object_w14 (Litex.callInOutput _object_w14))) (M.real_subset_complex _ h_220)))

          let _object_w17 := (let _wd_1_0 := _object_w15;
          let _wd_1_1 := _value_i6;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w15
            exact (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_220) (_atomic_wd_1_0).wd.2.2)) (M.real_subset_complex _ h_220)))

          have h_100 : (by
            let _equal_wd_1_0 := _object_w16
            let _equal_wd_1_1 := _object_w17
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ M.mulValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from h_99) (show (Litex.denote _value_i6) = (Litex.denote _value_i6) from (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          have h_101 : (by
            let _equal_wd_1_0 := _object_w17
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w17;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (by
                    let _quotient := (_object_w17).val.left
                    let _product := _equal_wd_1_0
                    have _child : (by
                      let _equal_wd_2_0 := _object_w15
                      let _equal_wd_2_1 := _object_w15
                      exact Litex.Same _equal_wd_2_1 _equal_wd_2_1) := (show @Eq M.Value _ _ from Eq.refl _)
                    have _conversion := Litex.sameDivIffSameMul _quotient.val.left _quotient.val.right _product.val.left _quotient.wd.1 _quotient.wd.2.1 _product.wd.1 _quotient.wd.2.2
                    exact ((_conversion.mp _child).symm))))
                )
            )
          exact ((h_100).trans h_101)
        )
      )
  )

noncomputable def _object_i8 := (Litex.number (M := M) (2 : ℂ))
theorem h_888 : Litex.In (_object_i8 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
      )
  )
theorem h_889 : Litex.Same (_object_i8 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))
      )
  )

theorem h_890 : ((prop_1 (M := M)) (_object_i8 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (Exists.intro (h_888 (M := M)) (Litex.notSameOfSame (Litex.number (M := M) (2 : ℂ)) (_object_i8 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((h_889 (M := M))).symm (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      )
  )

theorem h_944 : Litex.In (_object_i8 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_890 (M := M)) with ⟨h_2, h_1⟩; exact h_2)
      )
  )

theorem h_945 : ¬ Litex.Same (_object_i8 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_890 (M := M)) with ⟨h_2, h_1⟩; exact h_1)
      )
  )

noncomputable def _object_i9 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)))
theorem h_958 : Litex.Same (_object_i9 (M := M)) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))))
      )
  )

noncomputable def _object_w26 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (_object_i8 (M := M)) (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_888 (M := M))) (h_945 (M := M)))

theorem h_959 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)))
  let _equal_wd_1_1 := (_object_w26 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)));
        let _equal_wd_1_1 := (_object_w26 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote (_object_i8 (M := M)))) = (M.divValue (M.number (1 : ℂ)) (Litex.denote (_object_i8 (M := M)))) from by
          have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote (_object_i8 (M := M)))) = (M.divValue (M.number (1 : ℂ)) (Litex.denote (_object_i8 (M := M)))) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote (_object_i8 (M := M)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote (_object_i8 (M := M)))) = (M.divValue (M.number (1 : ℂ)) (Litex.denote (_object_i8 (M := M)))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
          let _wd_1_1 := (_object_i8 (M := M));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (h_888 (M := M)) (h_945 (M := M))))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_95 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote (_object_i8 (M := M)))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w27 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame (_object_i8 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_889 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_945 (M := M))))

theorem h_1513 : (by
  let _equal_wd_1_0 := (_object_w26 (M := M))
  let _equal_wd_1_1 := (_object_w27 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (congrArg₂ M.divValue (show (M.number (1 : ℂ)) = (M.number (1 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)) (show (Litex.denote (_object_i8 (M := M))) = (M.number (2 : ℂ)) from (h_889 (M := M))))
      )
  )

theorem h_1544 : (by
  have h_1545 : Litex.In (_object_i8 (M := M)) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (h_888 (M := M))
        )
    )
  exact (by
    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)));
    let _wd_1_1 := (_object_i8 (M := M));
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)))))) (M.real_subset_complex _ h_1545)))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_1545 : Litex.In (_object_i8 (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_888 (M := M))
                )
            )
          have h_1546 : ((prop_1 (M := M)) (_object_i8 (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_890 (M := M))
                )
            )
          have h_1556 :=
            (Classical.choose (show ((prop_1 (M := M)) (_object_i8 (M := M))) from h_1546))
          have h_1557 :=
            (Classical.choose_spec (show ((prop_1 (M := M)) (_object_i8 (M := M))) from h_1546))
          have h_1547 : Litex.Same (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)));
          let _wd_1_1 := (_object_i8 (M := M));
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)))))) (M.real_subset_complex _ h_1545))) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_98 (M := M)) (_object_i8 (M := M)) h_1545 h_1546)
                )
            )
          exact (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)));
        let _wd_1_1 := (_object_i8 (M := M));
        (Litex.mul _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M))) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_888 (M := M)) (h_945 (M := M)))))) (M.real_subset_complex _ h_1545)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_1547).trans (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))))))
        )
      )
  )

theorem h_1801 : (by
  let _equal_wd_1_1 := (_object_w27 (M := M))
  exact Litex.Same (_object_i9 (M := M)) _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (((((h_958 (M := M))).trans (h_959 (M := M)))).trans (h_1513 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_reciprocal_x5f_product_x5f_and_x5f_evaluation_x2f_statement_x2e_lit
