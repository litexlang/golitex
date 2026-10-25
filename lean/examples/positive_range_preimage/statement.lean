import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_range_x5f_preimage_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (fun (_raw_i2 : M.Value) => _raw_i2) (by
  intro _raw_i2 h_14 _positive_i2
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_14, _positive_i2⟩)
  have h_15 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i2 h_14)
        )
    )
  have h_16 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_15)
        )
    )
  have h_17 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_15) _litex_zero.symm)
        )
    )
  change Litex.In _value_i2 (Litex.RPos (M := M))
  exact h_14))
theorem h_27 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_28 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem _preimage_h_43 : ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (_member_i3 : M.mem (Litex.denote _value_i3) (Litex.positiveReal (M := M))), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))) := (by
  obtain ⟨_range_input, _range_domain, _range_eq⟩ := (Litex.inFnRange_iff (by
  have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((h_28 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
  have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) _raw_i2) → True := (by
    intro _raw_i2 h_23 _positive_i2
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23)
    have h_23 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_23, _positive_i2⟩)
    have h_24 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i2 h_23)
          )
      )
    have h_25 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_24)
          )
      )
    have h_26 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_24) _litex_zero.symm)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_27 (M := M)))
  exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))) _range_signature_0) (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_27 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))).2) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))))) (h_27 (M := M)))).mp (by
  let _atomic_wd_1_0 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_27 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))) ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))).2)
  let _atomic_wd_1_1 := (by
    have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((h_28 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
    have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) _raw_i2) → True := (by
      intro _raw_i2 h_23 _positive_i2
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23)
      have h_23 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_23, _positive_i2⟩)
      have h_24 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inRPos_positive _value_i2 h_23)
            )
        )
      have h_25 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_24)
            )
        )
      have h_26 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_24) _litex_zero.symm)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) (Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_27 (M := M)))
    exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2))) _range_signature_0)
  exact (Litex.callInFnRange _atomic_wd_1_0 _atomic_wd_1_1 (Litex.sameRefl (_object_i1 (M := M)))))
  obtain ⟨_range_members, _range_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.RPos (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.RPos (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i2)) _litex_input) _).mp _range_domain
  have _range_positive_i2 := _range_guard
  have _range_base_member_0 := _range_members
  have _range_member_0 := (Litex.positiveReal_members (M := M) (Litex.denote _range_input)).mpr ⟨_range_base_member_0, _range_positive_i2⟩
  exact ⟨(Litex.semanticObject (Litex.denote _range_input) (M.member_isSet _range_member_0)), _range_member_0, _range_eq⟩)

noncomputable def _value_i3 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((_preimage_h_43 (M := M)))

theorem h_39 : (M.mem (Litex.denote (_value_i3 (M := M))) (Litex.positiveReal (M := M))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((_preimage_h_43 (M := M))))))
      )
  )

theorem h_40 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (_value_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inRPos_positive (_value_i3 (M := M)) (h_39 (M := M)))
      )
  )

theorem h_41 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (_value_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (Litex.number (M := M) 0) (_value_i3 (M := M)) (h_40 (M := M)))
      )
  )

theorem h_42 : ¬ Litex.Same (_value_i3 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (_value_i3 (M := M)) (h_40 (M := M))) _litex_zero.symm)
      )
  )

theorem h_43 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote (_value_i3 (M := M))))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((_preimage_h_43 (M := M))))))
      )
  )

theorem h_44 : Litex.In (_value_i3 (M := M)) (Litex.RPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (h_39 (M := M))
      )
  )

theorem h_51 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (_value_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inRPos_positive (_value_i3 (M := M)) (h_44 (M := M)))
      )
  )

theorem h_52 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (_value_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (Litex.number (M := M) 0) (_value_i3 (M := M)) (h_51 (M := M)))
      )
  )

theorem h_53 : ¬ Litex.Same (_value_i3 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (_value_i3 (M := M)) (h_51 (M := M))) _litex_zero.symm)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_range_x5f_preimage_x2f_statement_x2e_lit
