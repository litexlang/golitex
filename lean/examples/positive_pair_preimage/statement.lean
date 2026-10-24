import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_pair_x5f_preimage_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn2Target (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue _raw_i2 _raw_i3)) (by
  rintro _raw_i2 _raw_i3 h_14 h_18 ⟨_positive_i2, _positive_i3⟩
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
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_18)
  have h_18 : Litex.In _value_i3 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i3).mpr ⟨h_18, _positive_i3⟩)
  have h_19 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i3 h_18)
        )
    )
  have h_20 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_19)
        )
    )
  have h_21 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_19) _litex_zero.symm)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.positiveRealToComplex _value_i2 h_14) (Litex.positiveRealToComplex _value_i3 h_18))
    exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 (Litex.positiveRealToComplex _value_i2 h_14) (Litex.positiveRealToComplex _value_i3 h_18))
    exact (Litex.inRPos_intro _atomic_wd_1_0 (by
      let _atomic_wd_2_0 := _atomic_wd_1_0
      exact (Litex.addInR _value_i2 _value_i3 (Litex.inRPos_real _value_i2 h_14) (Litex.inRPos_real _value_i3 h_18))) (by
      let _atomic_wd_2_1 := _atomic_wd_1_0
      exact (by
        let _litex_positive_result := _atomic_wd_2_1
        exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 h_15 h_19
      ))))))
theorem h_453 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_454 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem _preimage_h_476 : ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (_member_i4 : M.mem (Litex.denote _value_i4) (Litex.positiveReal (M := M))), ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (_member_i5 : M.mem (Litex.denote _value_i5) (Litex.positiveReal (M := M))), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (3 : ℂ))])) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)]))) := (by
  obtain ⟨_range_input, _range_domain, _range_eq⟩ := (Litex.inFnRange_iff (by
  have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) (Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) ((h_454 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
  have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (by
  have _checked_header : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))) _raw_i2 _raw_i3) → True := by
    rintro _raw_i2 _raw_i3 h_445 h_449 ⟨_positive_i2, _positive_i3⟩
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_445)
    have h_445 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_445, _positive_i2⟩)
    have h_446 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i2 h_445)
          )
      )
    have h_447 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_446)
          )
      )
    have h_448 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_446) _litex_zero.symm)
          )
      )
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_449)
    have h_449 : Litex.In _value_i3 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i3).mpr ⟨h_449, _positive_i3⟩)
    have h_450 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i3 h_449)
          )
      )
    have h_451 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_450)
          )
      )
    have h_452 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_450) _litex_zero.symm)
          )
      )
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) (Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_453 (M := M)))
  exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3))))) _range_signature_0) (Litex.call2Target Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_453 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))) (Litex.inRPos_real (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num) (by norm_num)))) (And.intro ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))).2 ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (3 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num) (by norm_num)))).2)) (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) (Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) (Litex.sameRefl (_object_i1 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3))))))) (h_453 (M := M)))).mp (by
  let _atomic_wd_1_0 := (Litex.call2Target Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_453 (M := M)) (Litex.inRPos_real (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))) (Litex.inRPos_real (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num) (by norm_num)))) (And.intro ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num) (by norm_num)))).2 ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (3 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num) (by norm_num)))).2))
  let _atomic_wd_1_1 := (by
    have _range_signature_0 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) (Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) ((h_454 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
    have _range_signature_1 : Litex.In (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (by
    have _checked_header : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))) _raw_i2 _raw_i3) → True := by
      rintro _raw_i2 _raw_i3 h_445 h_449 ⟨_positive_i2, _positive_i3⟩
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_445)
      have h_445 : Litex.In _value_i2 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i2).mpr ⟨h_445, _positive_i2⟩)
      have h_446 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inRPos_positive _value_i2 h_445)
            )
        )
      have h_447 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_446)
            )
        )
      have h_448 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_446) _litex_zero.symm)
            )
        )
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_449)
      have h_449 : Litex.In _value_i3 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i3).mpr ⟨h_449, _positive_i3⟩)
      have h_450 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inRPos_positive _value_i3 h_449)
            )
        )
      have h_451 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_450)
            )
        )
      have h_452 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_450) _litex_zero.symm)
            )
        )
      exact True.intro
    exact Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) (Litex.fnSet (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_453 (M := M)))
    exact Litex.fnRange (_object_i1 (M := M)) (Litex.FunctionSignature.twoTarget (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3))))) _range_signature_0)
  exact (Litex.call2InFnRange _atomic_wd_1_0 _atomic_wd_1_1 (Litex.sameRefl (_object_i1 (M := M)))))
  obtain ⟨_range_members, _range_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.RPos (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
  have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
  have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.RPos (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((Litex.positiveRealPredicate (M := M) _raw_i2)) ∧ ((Litex.positiveRealPredicate (M := M) _raw_i3)))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _range_domain
  rcases _range_guard with ⟨_range_positive_i2, _range_positive_i3⟩
  have _range_base_member_0 := (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _range_members (0 : Fin 2))
  have _range_member_0 := (Litex.positiveReal_members (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (1 : ℂ)))).mpr ⟨_range_base_member_0, _range_positive_i2⟩
  have _range_base_member_1 := (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _range_members (1 : Fin 2))
  have _range_member_1 := (Litex.positiveReal_members (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (2 : ℂ)))).mpr ⟨_range_base_member_1, _range_positive_i3⟩
  have _range_repack : Litex.denote _range_input = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (2 : ℂ)))] := by
    apply (Litex.FiniteFunction.reconstruct _range_members).trans
    apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
    funext i
    fin_cases i <;> norm_num [Litex.FiniteFunction.index]
  exact ⟨(Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (1 : ℂ))) (M.member_isSet _range_member_0)), _range_member_0, (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (2 : ℂ))) (M.member_isSet _range_member_1)), _range_member_1, (_range_eq.trans (congrArg (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M)))) _range_repack))⟩)

noncomputable def _value_i4 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((_preimage_h_476 (M := M)))

theorem h_468 : (M.mem (Litex.denote (_value_i4 (M := M))) (Litex.positiveReal (M := M))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((_preimage_h_476 (M := M))))))
      )
  )

theorem h_469 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (_value_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inRPos_positive (_value_i4 (M := M)) (h_468 (M := M)))
      )
  )

theorem h_470 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (_value_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (Litex.number (M := M) 0) (_value_i4 (M := M)) (h_469 (M := M)))
      )
  )

theorem h_471 : ¬ Litex.Same (_value_i4 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (_value_i4 (M := M)) (h_469 (M := M))) _litex_zero.symm)
      )
  )

noncomputable def _value_i5 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((_preimage_h_476 (M := M)))))))

theorem h_472 : (M.mem (Litex.denote (_value_i5 (M := M))) (Litex.positiveReal (M := M))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((_preimage_h_476 (M := M))))))))))
      )
  )

theorem h_473 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (_value_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inRPos_positive (_value_i5 (M := M)) (h_472 (M := M)))
      )
  )

theorem h_474 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (_value_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (Litex.number (M := M) 0) (_value_i5 (M := M)) (h_473 (M := M)))
      )
  )

theorem h_475 : ¬ Litex.Same (_value_i5 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (_value_i5 (M := M)) (h_473 (M := M))) _litex_zero.symm)
      )
  )

theorem h_476 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (2 : ℂ)), (M.number (3 : ℂ))])) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote (_value_i4 (M := M))), (Litex.denote (_value_i5 (M := M)))]))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((_preimage_h_476 (M := M))))))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_pair_x5f_preimage_x2f_statement_x2e_lit
