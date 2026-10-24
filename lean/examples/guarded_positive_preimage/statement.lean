import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_guarded_x5f_positive_x5f_preimage_x2f_statement_x2e_lit

universe u v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) (fun (_raw_i2 : M.Value) => _raw_i2) (by
  rintro _raw_i2 h_135 ⟨_positive_i2, h_1, h_2⟩
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_135)
  have h_135 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_135, _positive_i2⟩)
  have h_136 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i2 h_135)
        )
    )
  have h_137 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_136)
        )
    )
  have h_138 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_136) _litex_zero.symm)
        )
    )
  have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i2 = (M.number (1 : ℂ))))
            exact h_1)
        )
    )
  have h_2 : Litex.Lt _value_i2 (Litex.number (M := M) (5 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)
            exact h_2)
        )
    )
  have h_164 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i2 (Litex.number (M := M) (5 : ℂ)) h_137 h_2)
        )
    )
  change Litex.In _value_i2 (Litex.RPos (M := M))
  exact h_135))
theorem h_200 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_201 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem _preimage_h_232 : ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (_member_i5 : M.mem (Litex.denote _value_i5) (Litex.positiveReal (M := M))), ∃ (h_224 : (¬ ((Litex.denote _value_i5) = (M.number (1 : ℂ))))), ∃ (h_225 : (∃ (_r _s : ℝ), (Litex.denote _value_i5) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5))) := (by
  obtain ⟨_range_input, _range_domain, _range_eq⟩ := (Litex.inFnRange_iff (by
  have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((h_201 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
  have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (by
  have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _raw_i2) → True := by
    rintro _raw_i2 h_170 ⟨_positive_i2, h_1, h_2⟩
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_170)
    have h_170 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_170, _positive_i2⟩)
    have h_171 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i2 h_170)
          )
      )
    have h_172 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_171)
          )
      )
    have h_173 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_171) _litex_zero.symm)
          )
      )
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i2 = (M.number (1 : ℂ))))
              exact h_1)
          )
      )
    have h_2 : Litex.Lt _value_i2 (Litex.number (M := M) (5 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)
              exact h_2)
          )
      )
    have h_199 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i2 (Litex.number (M := M) (5 : ℂ)) h_172 h_2)
          )
      )
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_200 (M := M)))
  exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) _range_signature_0) (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_200 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))) (And.intro ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))).2 (And.intro (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (2 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))))) (h_200 (M := M)))).mp (by
  let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_200 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))) (And.intro ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))).2 (And.intro (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (2 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)) = (5 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
  let _atomic_wd_1_1 := (by
    have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((h_201 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
    have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (by
    have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _raw_i2) → True := by
      rintro _raw_i2 h_170 ⟨_positive_i2, h_1, h_2⟩
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_170)
      have h_170 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_170, _positive_i2⟩)
      have h_171 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inRPos_positive _value_i2 h_170)
            )
        )
      have h_172 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_171)
            )
        )
      have h_173 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_171) _litex_zero.symm)
            )
        )
      have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i2 = (M.number (1 : ℂ))))
                exact h_1)
            )
        )
      have h_2 : Litex.Lt _value_i2 (Litex.number (M := M) (5 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)
                exact h_2)
            )
        )
      have h_199 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i2 (Litex.number (M := M) (5 : ℂ)) h_172 h_2)
            )
        )
      exact True.intro
    exact Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_200 (M := M)))
    exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) _range_signature_0)
  exact (Litex.callInFnRange _atomic_wd_1_0 _atomic_wd_1_1 (Litex.sameRefl (_object_i1 (M := M)))))
  obtain ⟨_range_members, _range_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.RPos (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.RPos (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _litex_input) _).mp _range_domain
  rcases _range_guard with ⟨_range_positive_i2, h_224, h_225⟩
  have _range_base_member_0 := _range_members
  have _range_member_0 := (Litex.positiveReal_members (M := M) (Litex.denote _range_input)).mpr ⟨_range_base_member_0, _range_positive_i2⟩
  exact ⟨(Litex.semanticObject (Litex.denote _range_input) (M.member_isSet _range_member_0)), _range_member_0, h_224, h_225, _range_eq⟩)

noncomputable def _value_i5 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((_preimage_h_232 (M := M)))

theorem h_220 : (M.mem (Litex.denote (_value_i5 (M := M))) (Litex.positiveReal (M := M))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((_preimage_h_232 (M := M))))))
      )
  )

theorem h_221 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (_value_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inRPos_positive (_value_i5 (M := M)) (h_220 (M := M)))
      )
  )

theorem h_222 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (_value_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (Litex.number (M := M) 0) (_value_i5 (M := M)) (h_221 (M := M)))
      )
  )

theorem h_223 : ¬ Litex.Same (_value_i5 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (_value_i5 (M := M)) (h_221 (M := M))) _litex_zero.symm)
      )
  )

theorem h_224 : (¬ ((Litex.denote (_value_i5 (M := M))) = (M.number (1 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((_preimage_h_232 (M := M))))))))
      )
  )

theorem h_225 : (∃ (_r _s : ℝ), (Litex.denote (_value_i5 (M := M))) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((_preimage_h_232 (M := M))))))))))
      )
  )

theorem h_231 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (_value_i5 (M := M)) (Litex.number (M := M) (5 : ℂ)) (h_222 (M := M)) (h_225 (M := M)))
      )
  )

theorem h_232 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote (_value_i5 (M := M))))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((_preimage_h_232 (M := M))))))))))
      )
  )

theorem h_233 : ¬ Litex.Same (_value_i5 (M := M)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_224 (M := M))
      )
  )

theorem h_242 : Litex.Lt (_value_i5 (M := M)) (Litex.number (M := M) (5 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_225 (M := M))
      )
  )

theorem h_254 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (_value_i5 (M := M)) (Litex.number (M := M) (5 : ℂ)) (h_222 (M := M)) (h_242 (M := M)))
      )
  )

theorem h_256 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_261 : Litex.In _value_i6 (by
  have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((h_201 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
  have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (by
  have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _raw_i2) → True := by
    rintro _raw_i2 h_170 ⟨_positive_i2, h_1, h_2⟩
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_170)
    have h_170 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_170, _positive_i2⟩)
    have h_171 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i2 h_170)
          )
      )
    have h_172 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_171)
          )
      )
    have h_173 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_171) _litex_zero.symm)
          )
      )
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i2 = (M.number (1 : ℂ))))
              exact h_1)
          )
      )
    have h_2 : Litex.Lt _value_i2 (Litex.number (M := M) (5 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)
              exact h_2)
          )
      )
    have h_199 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i2 (Litex.number (M := M) (5 : ℂ)) h_172 h_2)
          )
      )
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_200 (M := M)))
  exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) _range_signature_0)), Litex.In _value_i6 (Litex.RPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_261
          have h_262 : Litex.In _value_i6 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.fnRangeInOutput (by
                    have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((h_201 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
                    have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (by
                    have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _raw_i2) → True := by
                      rintro _raw_i2 h_170 ⟨_positive_i2, h_1, h_2⟩
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_170)
                      have h_170 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_170, _positive_i2⟩)
                      have h_171 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inRPos_positive _value_i2 h_170)
                            )
                        )
                      have h_172 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_171)
                            )
                        )
                      have h_173 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_171) _litex_zero.symm)
                            )
                        )
                      have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i2 = (M.number (1 : ℂ))))
                                exact h_1)
                            )
                        )
                      have h_2 : Litex.Lt _value_i2 (Litex.number (M := M) (5 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)
                                exact h_2)
                            )
                        )
                      have h_199 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i2 (Litex.number (M := M) (5 : ℂ)) h_172 h_2)
                            )
                        )
                      exact True.intro
                    exact Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_200 (M := M)))
                    exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) _range_signature_0) _value_i6 (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))))) (h_200 (M := M))) h_261)
                )
            )
          have h_266 : ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (_member_i9 : M.mem (Litex.denote _value_i9) (Litex.positiveReal (M := M))), ∃ (h_263 : (¬ ((Litex.denote _value_i9) = (M.number (1 : ℂ))))), ∃ (h_264 : (∃ (_r _s : ℝ), (Litex.denote _value_i9) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)), ((Litex.denote _value_i6) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    obtain ⟨_range_input, _range_domain, _range_eq⟩ := (Litex.inFnRange_iff (by
                    have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((h_201 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
                    have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (by
                    have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _raw_i2) → True := by
                      rintro _raw_i2 h_170 ⟨_positive_i2, h_1, h_2⟩
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_170)
                      have h_170 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_170, _positive_i2⟩)
                      have h_171 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inRPos_positive _value_i2 h_170)
                            )
                        )
                      have h_172 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_171)
                            )
                        )
                      have h_173 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_171) _litex_zero.symm)
                            )
                        )
                      have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i2 = (M.number (1 : ℂ))))
                                exact h_1)
                            )
                        )
                      have h_2 : Litex.Lt _value_i2 (Litex.number (M := M) (5 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)
                                exact h_2)
                            )
                        )
                      have h_199 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i2 (Litex.number (M := M) (5 : ℂ)) h_172 h_2)
                            )
                        )
                      exact True.intro
                    exact Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_200 (M := M)))
                    exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) _range_signature_0) _value_i6 (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))))) (h_200 (M := M)))).mp h_261
                    obtain ⟨_range_members, _range_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.RPos (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.RPos (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _litex_input) _).mp _range_domain
                    rcases _range_guard with ⟨_range_positive_i2, h_263, h_264⟩
                    have _range_base_member_0 := _range_members
                    have _range_member_0 := (Litex.positiveReal_members (M := M) (Litex.denote _range_input)).mpr ⟨_range_base_member_0, _range_positive_i2⟩
                    exact ⟨(Litex.semanticObject (Litex.denote _range_input) (M.member_isSet _range_member_0)), _range_member_0, h_263, h_264, _range_eq⟩)
                )
            )
          have h_271 : Litex.In _value_i6 (by
            have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((h_201 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
            have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (by
            have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _raw_i2) → True := by
              rintro _raw_i2 h_170 ⟨_positive_i2, h_1, h_2⟩
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_170)
              have h_170 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_170, _positive_i2⟩)
              have h_171 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inRPos_positive _value_i2 h_170)
                    )
                )
              have h_172 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_171)
                    )
                )
              have h_173 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_171) _litex_zero.symm)
                    )
                )
              have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i2 = (M.number (1 : ℂ))))
                        exact h_1)
                    )
                )
              have h_2 : Litex.Lt _value_i2 (Litex.number (M := M) (5 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)
                        exact h_2)
                    )
                )
              have h_199 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i2 (Litex.number (M := M) (5 : ℂ)) h_172 h_2)
                    )
                )
              exact True.intro
            exact Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_200 (M := M)))
            exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) _range_signature_0) :=
            (by
              litex_checked_step =>
                exact (
                  h_261
                )
            )
          have h_272 : Litex.In _value_i6 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.fnRangeInOutput (by
                    have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((h_201 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
                    have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (by
                    have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _raw_i2) → True := by
                      rintro _raw_i2 h_170 ⟨_positive_i2, h_1, h_2⟩
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_170)
                      have h_170 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_170, _positive_i2⟩)
                      have h_171 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inRPos_positive _value_i2 h_170)
                            )
                        )
                      have h_172 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_171)
                            )
                        )
                      have h_173 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_171) _litex_zero.symm)
                            )
                        )
                      have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i2 = (M.number (1 : ℂ))))
                                exact h_1)
                            )
                        )
                      have h_2 : Litex.Lt _value_i2 (Litex.number (M := M) (5 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)
                                exact h_2)
                            )
                        )
                      have h_199 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i2 (Litex.number (M := M) (5 : ℂ)) h_172 h_2)
                            )
                        )
                      exact True.intro
                    exact Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_200 (M := M)))
                    exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) _range_signature_0) _value_i6 (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))))) (h_200 (M := M))) h_271)
                )
            )
          have h_276 : ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (_member_i10 : M.mem (Litex.denote _value_i10) (Litex.positiveReal (M := M))), ∃ (h_273 : (¬ ((Litex.denote _value_i10) = (M.number (1 : ℂ))))), ∃ (h_274 : (∃ (_r _s : ℝ), (Litex.denote _value_i10) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)), ((Litex.denote _value_i6) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i10))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    obtain ⟨_range_input, _range_domain, _range_eq⟩ := (Litex.inFnRange_iff (by
                    have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((h_201 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
                    have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (by
                    have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _raw_i2) → True := by
                      rintro _raw_i2 h_170 ⟨_positive_i2, h_1, h_2⟩
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_170)
                      have h_170 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_170, _positive_i2⟩)
                      have h_171 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inRPos_positive _value_i2 h_170)
                            )
                        )
                      have h_172 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_171)
                            )
                        )
                      have h_173 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_171) _litex_zero.symm)
                            )
                        )
                      have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i2 = (M.number (1 : ℂ))))
                                exact h_1)
                            )
                        )
                      have h_2 : Litex.Lt _value_i2 (Litex.number (M := M) (5 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)
                                exact h_2)
                            )
                        )
                      have h_199 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i2 (Litex.number (M := M) (5 : ℂ)) h_172 h_2)
                            )
                        )
                      exact True.intro
                    exact Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_200 (M := M)))
                    exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) _range_signature_0) _value_i6 (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))))) (h_200 (M := M)))).mp h_271
                    obtain ⟨_range_members, _range_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.RPos (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.RPos (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _litex_input) _).mp _range_domain
                    rcases _range_guard with ⟨_range_positive_i2, h_273, h_274⟩
                    have _range_base_member_0 := _range_members
                    have _range_member_0 := (Litex.positiveReal_members (M := M) (Litex.denote _range_input)).mpr ⟨_range_base_member_0, _range_positive_i2⟩
                    exact ⟨(Litex.semanticObject (Litex.denote _range_input) (M.member_isSet _range_member_0)), _range_member_0, h_273, h_274, _range_eq⟩)
                )
            )
          have _preimage_h_293 : ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (_member_i7 : M.mem (Litex.denote _value_i7) (Litex.positiveReal (M := M))), ∃ (h_285 : (¬ ((Litex.denote _value_i7) = (M.number (1 : ℂ))))), ∃ (h_286 : (∃ (_r _s : ℝ), (Litex.denote _value_i7) = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)), ((Litex.denote _value_i6) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7))) := (by
            obtain ⟨_range_input, _range_domain, _range_eq⟩ := (Litex.inFnRange_iff (by
            have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((h_201 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
            have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (by
            have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _raw_i2) → True := by
              rintro _raw_i2 h_170 ⟨_positive_i2, h_1, h_2⟩
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_170)
              have h_170 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_170, _positive_i2⟩)
              have h_171 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inRPos_positive _value_i2 h_170)
                    )
                )
              have h_172 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_171)
                    )
                )
              have h_173 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_171) _litex_zero.symm)
                    )
                )
              have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i2 = (M.number (1 : ℂ))))
                        exact h_1)
                    )
                )
              have h_2 : Litex.Lt _value_i2 (Litex.number (M := M) (5 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)
                        exact h_2)
                    )
                )
              have h_199 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i2 (Litex.number (M := M) (5 : ℂ)) h_172 h_2)
                    )
                )
              exact True.intro
            exact Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_200 (M := M)))
            exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) _range_signature_0) _value_i6 (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))))) (h_200 (M := M)))).mp (by
            let _atomic_wd_1_1 := (by
              have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((h_201 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
              have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (by
              have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _raw_i2) → True := by
                rintro _raw_i2 h_170 ⟨_positive_i2, h_1, h_2⟩
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_170)
                have h_170 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_170, _positive_i2⟩)
                have h_171 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inRPos_positive _value_i2 h_170)
                      )
                  )
                have h_172 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_171)
                      )
                  )
                have h_173 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_171) _litex_zero.symm)
                      )
                  )
                have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          change (¬ (_raw_i2 = (M.number (1 : ℂ))))
                          exact h_1)
                      )
                  )
                have h_2 : Litex.Lt _value_i2 (Litex.number (M := M) (5 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          change (∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)
                          exact h_2)
                      )
                  )
                have h_199 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i2 (Litex.number (M := M) (5 : ℂ)) h_172 h_2)
                      )
                  )
                exact True.intro
              exact Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_200 (M := M)))
              exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s))))))) _range_signature_0)
            exact h_271)
            obtain ⟨_range_members, _range_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.RPos (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.RPos (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((((¬ (_raw_i2 = (M.number (1 : ℂ))))) ∧ ((∃ (_r _s : ℝ), _raw_i2 = M.number (_r : ℂ) ∧ (M.number (5 : ℂ)) = M.number (_s : ℂ) ∧ _r < _s)))))) _litex_input) _).mp _range_domain
            rcases _range_guard with ⟨_range_positive_i2, h_285, h_286⟩
            have _range_base_member_0 := _range_members
            have _range_member_0 := (Litex.positiveReal_members (M := M) (Litex.denote _range_input)).mpr ⟨_range_base_member_0, _range_positive_i2⟩
            exact ⟨(Litex.semanticObject (Litex.denote _range_input) (M.member_isSet _range_member_0)), _range_member_0, h_285, h_286, _range_eq⟩)

          rcases _preimage_h_293 with ⟨_value_i7, h_281, h_285, h_286, h_293⟩

          have h_282 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i7 h_281)
                )
            )

          have h_283 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_282)
                )
            )

          have h_284 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_282) _litex_zero.symm)
                )
            )

          have h_292 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i7 (Litex.number (M := M) (5 : ℂ)) h_283 h_286)
                )
            )
          have h_258 : Litex.In _value_i7 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_281
                )
            )

          have h_302 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i7 h_258)
                )
            )

          have h_303 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_302)
                )
            )

          have h_304 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_302) _litex_zero.symm)
                )
            )
          have h_259 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_285
                )
            )
          have h_260 : Litex.Lt _value_i7 (Litex.number (M := M) (5 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_286
                )
            )

          have h_324 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i7 (Litex.number (M := M) (5 : ℂ)) h_283 h_260)
                )
            )
          exact h_272
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_guarded_x5f_positive_x5f_preimage_x2f_statement_x2e_lit
