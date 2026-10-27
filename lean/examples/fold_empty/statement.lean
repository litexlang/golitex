import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_fold_x5f_empty_x2f_statement_x2e_lit

universe u v1 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.Z (M := M))), (by
  let _object_w2 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
    intro _raw_i2 h_29 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_29)
    have h_29 : Litex.In _value_i2 (Litex.Z (M := M)) := h_29
    change Litex.In _value_i2 (Litex.Z (M := M))
    exact h_29));
  let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => (M.subValue _raw_i3 _raw_i4)) (by
    intro _raw_i3 _raw_i4 h_48 h_49 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_48)
    have h_48 : Litex.In _value_i3 (Litex.Z (M := M)) := h_48
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_49)
    have h_49 : Litex.In _value_i4 (Litex.Z (M := M)) := h_49
    change (by
      let _atomic_wd_1_0 := (Litex.sub _value_i3 _value_i4 (Litex.integerToComplex _value_i3 h_48) (Litex.integerToComplex _value_i4 h_49))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.sub _value_i3 _value_i4 (Litex.integerToComplex _value_i3 h_48) (Litex.integerToComplex _value_i4 h_49))
      exact (Litex.subInZ _value_i3 _value_i4 h_48 h_49))));
  let _wd_1_4 := _value_i1;
  (let h_151 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
  let h_154 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
  let h_157 : Litex.In _wd_1_4 (Litex.Z (M := M)) := h_15;
  let h_162 : Litex.Same _wd_1_0 _wd_1_0 := (show @Eq M.Value _ _ from Eq.refl _);
  let h_163 : Litex.Same _wd_1_1 _wd_1_1 := (show @Eq M.Value _ _ from Eq.refl _);
  Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) h_151 h_154 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_157 (fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty _wd_1_0 _wd_1_1 (1 : ℤ) (0 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_162) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_163) (by decide) k hlow hhigh))))
  exact (by
    let _equal_wd_1_0 := _object_w2
    exact Litex.Same _equal_wd_1_0 _value_i1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15
          let _object_w2 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
            intro _raw_i2 h_29 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_29)
            have h_29 : Litex.In _value_i2 (Litex.Z (M := M)) := h_29
            change Litex.In _value_i2 (Litex.Z (M := M))
            exact h_29));
          let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => True) (fun (_raw_i3 : M.Value) (_raw_i4 : M.Value) => (M.subValue _raw_i3 _raw_i4)) (by
            intro _raw_i3 _raw_i4 h_48 h_49 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_48)
            have h_48 : Litex.In _value_i3 (Litex.Z (M := M)) := h_48
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_49)
            have h_49 : Litex.In _value_i4 (Litex.Z (M := M)) := h_49
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i3 _value_i4 (Litex.integerToComplex _value_i3 h_48) (Litex.integerToComplex _value_i4 h_49))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i3 _value_i4 (Litex.integerToComplex _value_i3 h_48) (Litex.integerToComplex _value_i4 h_49))
              exact (Litex.subInZ _value_i3 _value_i4 h_48 h_49))));
          let _wd_1_4 := _value_i1;
          (let h_151 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
          let h_154 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
          let h_157 : Litex.In _wd_1_4 (Litex.Z (M := M)) := h_15;
          let h_162 : Litex.Same _wd_1_0 _wd_1_0 := (show @Eq M.Value _ _ from Eq.refl _);
          let h_163 : Litex.Same _wd_1_1 _wd_1_1 := (show @Eq M.Value _ _ from Eq.refl _);
          Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) h_151 h_154 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_157 (fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty _wd_1_0 _wd_1_1 (1 : ℤ) (0 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_162) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_163) (by decide) k hlow hhigh))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from ((Litex.rangeFoldEmptyOfLt _equal_wd_1_0 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))))
                )
            )
          exact h_1
        )
      )
  )

theorem h_185 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_199 : Litex.In _value_i5 (Litex.Z (M := M))), (by
  let _object_w18 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0);
  let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => _raw_i6) (by
    intro _raw_i6 h_213 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_213)
    have h_213 : Litex.In _value_i6 (Litex.Z (M := M)) := h_213
    change Litex.In _value_i6 (Litex.Z (M := M))
    exact h_213));
  let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
    intro _raw_i7 _raw_i8 h_232 h_233 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_232)
    have h_232 : Litex.In _value_i7 (Litex.Z (M := M)) := h_232
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_233)
    have h_233 : Litex.In _value_i8 (Litex.Z (M := M)) := h_233
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_232) (Litex.integerToComplex _value_i8 h_233))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_232) (Litex.integerToComplex _value_i8 h_233))
      exact (Litex.addInZ _value_i7 _value_i8 h_232 h_233))));
  let _wd_1_3 := _value_i5;
  (let h_335 : (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact (let _finite_tail_0 := _atomic_wd_1_0;
    have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
    _finite_0));
  let h_336 : Litex.In _wd_1_3 (Litex.Z (M := M)) := h_199;
  let h_345 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_358 : Litex.In _value_i9 (Litex.Z (M := M))) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_359 : Litex.In _value_i10 (Litex.Z (M := M))), (by
    let _object_w4 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_373 h_374 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_373)
      have h_373 : Litex.In _value_i7 (Litex.Z (M := M)) := h_373
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_374)
      have h_374 : Litex.In _value_i8 (Litex.Z (M := M)) := h_374
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_373) (Litex.integerToComplex _value_i8 h_374))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_373) (Litex.integerToComplex _value_i8 h_374))
        exact (Litex.addInZ _value_i7 _value_i8 h_373 h_374))));
    let _wd_2_1 := _value_i9;
    let _wd_2_2 := _value_i10;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_358 h_359 True.intro))
    let _object_w5 := (Litex.add _value_i9 _value_i10 (Litex.integerToComplex _value_i9 h_358) (Litex.integerToComplex _value_i10 h_359))
    let _object_w6 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_1637 h_1638 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1637)
      have h_1637 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1637
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1638)
      have h_1638 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1638
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1637) (Litex.integerToComplex _value_i8 h_1638))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1637) (Litex.integerToComplex _value_i8 h_1638))
        exact (Litex.addInZ _value_i7 _value_i8 h_1637 h_1638))));
    let _wd_2_1 := _value_i10;
    let _wd_2_2 := _value_i9;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_359 h_358 True.intro))
    let _object_w7 := (Litex.add _value_i10 _value_i9 (Litex.integerToComplex _value_i10 h_359) (Litex.integerToComplex _value_i9 h_358))
    exact (((by
      let _equal_wd_1_0 := _object_w4
      let _equal_wd_1_1 := _object_w5
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
      let _equal_wd_1_0 := _object_w6
      let _equal_wd_1_1 := _object_w7
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
      let _equal_wd_1_0 := _object_w5
      let _equal_wd_1_1 := _object_w7
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
      let _equal_wd_1_0 := _object_w4
      let _equal_wd_1_1 := _object_w6
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
  ) := (by
    intro _Host_i9 _rep_i9 _value_i9 h_358 _Host_i10 _rep_i10 _value_i10 h_359
    let _object_w4 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_373 h_374 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_373)
      have h_373 : Litex.In _value_i7 (Litex.Z (M := M)) := h_373
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_374)
      have h_374 : Litex.In _value_i8 (Litex.Z (M := M)) := h_374
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_373) (Litex.integerToComplex _value_i8 h_374))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_373) (Litex.integerToComplex _value_i8 h_374))
        exact (Litex.addInZ _value_i7 _value_i8 h_373 h_374))));
    let _wd_2_1 := _value_i9;
    let _wd_2_2 := _value_i10;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_358 h_359 True.intro))
    let _object_w5 := (Litex.add _value_i9 _value_i10 (Litex.integerToComplex _value_i9 h_358) (Litex.integerToComplex _value_i10 h_359))
    have h_341 : (by
      let _equal_wd_1_0 := _object_w4
      let _equal_wd_1_1 := _object_w5
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) from by
              let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                intro _raw_i7 _raw_i8 h_1220 h_1221 _
                let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1220)
                have h_1220 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1220
                let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1221)
                have h_1221 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1221
                change (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1220) (Litex.integerToComplex _value_i8 h_1221))
                  exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1220) (Litex.integerToComplex _value_i8 h_1221))
                  exact (Litex.addInZ _value_i7 _value_i8 h_1220 h_1221))));
              let _wd_2_1 := _value_i9;
              let _wd_2_2 := _value_i10;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_358 h_359 True.intro))
              let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                intro _raw_i7 _raw_i8 h_1387 h_1388 _
                let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1387)
                have h_1387 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1387
                let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1388)
                have h_1388 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1388
                change (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1387) (Litex.integerToComplex _value_i8 h_1388))
                  exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1387) (Litex.integerToComplex _value_i8 h_1388))
                  exact (Litex.addInZ _value_i7 _value_i8 h_1387 h_1388))));
              let _wd_2_1 := _value_i9;
              let _wd_2_2 := _value_i10;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_358 h_359 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) from rfl))
            ))).trans _litex_residual)
          )
      )
    let _object_w6 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_1637 h_1638 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1637)
      have h_1637 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1637
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1638)
      have h_1638 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1638
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1637) (Litex.integerToComplex _value_i8 h_1638))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1637) (Litex.integerToComplex _value_i8 h_1638))
        exact (Litex.addInZ _value_i7 _value_i8 h_1637 h_1638))));
    let _wd_2_1 := _value_i10;
    let _wd_2_2 := _value_i9;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_359 h_358 True.intro))
    let _object_w7 := (Litex.add _value_i10 _value_i9 (Litex.integerToComplex _value_i10 h_359) (Litex.integerToComplex _value_i9 h_358))
    have h_342 : (by
      let _equal_wd_1_0 := _object_w6
      let _equal_wd_1_1 := _object_w7
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i9)])) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i9)) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i9)) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i9)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i9)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i9)])) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i9)) from by
              let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                intro _raw_i7 _raw_i8 h_2484 h_2485 _
                let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_2484)
                have h_2484 : Litex.In _value_i7 (Litex.Z (M := M)) := h_2484
                let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_2485)
                have h_2485 : Litex.In _value_i8 (Litex.Z (M := M)) := h_2485
                change (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2484) (Litex.integerToComplex _value_i8 h_2485))
                  exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2484) (Litex.integerToComplex _value_i8 h_2485))
                  exact (Litex.addInZ _value_i7 _value_i8 h_2484 h_2485))));
              let _wd_2_1 := _value_i10;
              let _wd_2_2 := _value_i9;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_359 h_358 True.intro))
              let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                intro _raw_i7 _raw_i8 h_2651 h_2652 _
                let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_2651)
                have h_2651 : Litex.In _value_i7 (Litex.Z (M := M)) := h_2651
                let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_2652)
                have h_2652 : Litex.In _value_i8 (Litex.Z (M := M)) := h_2652
                change (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2651) (Litex.integerToComplex _value_i8 h_2652))
                  exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2651) (Litex.integerToComplex _value_i8 h_2652))
                  exact (Litex.addInZ _value_i7 _value_i8 h_2651 h_2652))));
              let _wd_2_1 := _value_i10;
              let _wd_2_2 := _value_i9;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_359 h_358 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i9)) from rfl))
            ))).trans _litex_residual)
          )
      )
    have h_343 : (by
      let _equal_wd_1_0 := _object_w5
      let _equal_wd_1_1 := _object_w7
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i9 (Litex.integerToComplex _value_i9 h_358)) + (Litex.NativeBridge.asComplex _value_i10 (Litex.integerToComplex _value_i10 h_359))) ((Litex.NativeBridge.asComplex _value_i10 (Litex.integerToComplex _value_i10 h_359)) + (Litex.NativeBridge.asComplex _value_i9 (Litex.integerToComplex _value_i9 h_358))) (Litex.NativeBridge.denoteAdd _value_i9 _value_i10 (_object_w5).wd.1 (_object_w5).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.integerToComplex _value_i9 h_358)) (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.integerToComplex _value_i10 h_359))) (Litex.NativeBridge.denoteAdd _value_i10 _value_i9 (_object_w7).wd.1 (_object_w7).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.integerToComplex _value_i10 h_359)) (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.integerToComplex _value_i9 h_358))) (by ring!))
          )
      )
    have h_344 : (by
      let _equal_wd_1_0 := _object_w4
      let _equal_wd_1_1 := _object_w6
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            ((((h_341).trans h_343)).trans (h_342).symm)
          )
      )
    exact (And.intro h_341 (And.intro h_342 (And.intro h_343 h_344)))
  );
  let h_2901 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_2914 : Litex.In _value_i9 (Litex.Z (M := M))) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_2915 : Litex.In _value_i10 (Litex.Z (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_2916 : Litex.In _value_i11 (Litex.Z (M := M))), (by
    let _object_w8 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_2930 h_2931 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_2930)
      have h_2930 : Litex.In _value_i7 (Litex.Z (M := M)) := h_2930
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_2931)
      have h_2931 : Litex.In _value_i8 (Litex.Z (M := M)) := h_2931
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2930) (Litex.integerToComplex _value_i8 h_2931))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2930) (Litex.integerToComplex _value_i8 h_2931))
        exact (Litex.addInZ _value_i7 _value_i8 h_2930 h_2931))));
    let _wd_2_1 := _value_i9;
    let _wd_2_2 := _value_i10;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 h_2915 True.intro))
    let _object_w9 := (Litex.add _value_i9 _value_i10 (Litex.integerToComplex _value_i9 h_2914) (Litex.integerToComplex _value_i10 h_2915))
    let _object_w10 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_4358 h_4359 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_4358)
      have h_4358 : Litex.In _value_i7 (Litex.Z (M := M)) := h_4358
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4359)
      have h_4359 : Litex.In _value_i8 (Litex.Z (M := M)) := h_4359
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_4358) (Litex.integerToComplex _value_i8 h_4359))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_4358) (Litex.integerToComplex _value_i8 h_4359))
        exact (Litex.addInZ _value_i7 _value_i8 h_4358 h_4359))));
    let _wd_2_1 := _value_i10;
    let _wd_2_2 := _value_i11;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2915 h_2916 True.intro))
    let _object_w11 := (Litex.add _value_i10 _value_i11 (Litex.integerToComplex _value_i10 h_2915) (Litex.integerToComplex _value_i11 h_2916))
    let _object_w12 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_5814 h_5815 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_5814)
      have h_5814 : Litex.In _value_i7 (Litex.Z (M := M)) := h_5814
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_5815)
      have h_5815 : Litex.In _value_i8 (Litex.Z (M := M)) := h_5815
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5814) (Litex.integerToComplex _value_i8 h_5815))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5814) (Litex.integerToComplex _value_i8 h_5815))
        exact (Litex.addInZ _value_i7 _value_i8 h_5814 h_5815))));
    let _wd_2_1 := _object_w8;
    let _wd_2_2 := _value_i11;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
      let _atomic_wd_1_0 := _object_w8
      exact (Litex.inOfSame _object_w8 _object_w8 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w8) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w8))) h_2916 True.intro))
    let _object_w13 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_6046 h_6047 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_6046)
      have h_6046 : Litex.In _value_i7 (Litex.Z (M := M)) := h_6046
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_6047)
      have h_6047 : Litex.In _value_i8 (Litex.Z (M := M)) := h_6047
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6046) (Litex.integerToComplex _value_i8 h_6047))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6046) (Litex.integerToComplex _value_i8 h_6047))
        exact (Litex.addInZ _value_i7 _value_i8 h_6046 h_6047))));
    let _wd_2_1 := _object_w9;
    let _wd_2_2 := _value_i11;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
      let _atomic_wd_1_0 := _object_w9
      exact (Litex.addInZ _value_i9 _value_i10 h_2914 h_2915)) h_2916 True.intro))
    let _object_w14 := (let _wd_2_0 := _object_w9;
    let _wd_2_1 := _value_i11;
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_1_0 := _object_w9
      exact (Litex.addInC _value_i9 _value_i10 (Litex.integerToComplex _value_i9 h_2914) (Litex.integerToComplex _value_i10 h_2915))) (Litex.integerToComplex _wd_2_1 h_2916)))
    let _object_w15 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_6892 h_6893 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_6892)
      have h_6892 : Litex.In _value_i7 (Litex.Z (M := M)) := h_6892
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_6893)
      have h_6893 : Litex.In _value_i8 (Litex.Z (M := M)) := h_6893
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6892) (Litex.integerToComplex _value_i8 h_6893))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6892) (Litex.integerToComplex _value_i8 h_6893))
        exact (Litex.addInZ _value_i7 _value_i8 h_6892 h_6893))));
    let _wd_2_1 := _value_i9;
    let _wd_2_2 := _object_w10;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 (by
      let _atomic_wd_1_0 := _object_w10
      exact (Litex.inOfSame _object_w10 _object_w10 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w10) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w10))) True.intro))
    let _object_w16 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_7120 h_7121 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_7120)
      have h_7120 : Litex.In _value_i7 (Litex.Z (M := M)) := h_7120
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_7121)
      have h_7121 : Litex.In _value_i8 (Litex.Z (M := M)) := h_7121
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_7120) (Litex.integerToComplex _value_i8 h_7121))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_7120) (Litex.integerToComplex _value_i8 h_7121))
        exact (Litex.addInZ _value_i7 _value_i8 h_7120 h_7121))));
    let _wd_2_1 := _value_i9;
    let _wd_2_2 := _object_w11;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 (by
      let _atomic_wd_1_0 := _object_w11
      exact (Litex.addInZ _value_i10 _value_i11 h_2915 h_2916)) True.intro))
    let _object_w17 := (let _wd_2_0 := _value_i9;
    let _wd_2_1 := _object_w11;
    (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_2914) (by
      let _atomic_wd_1_0 := _object_w11
      exact (Litex.addInC _value_i10 _value_i11 (Litex.integerToComplex _value_i10 h_2915) (Litex.integerToComplex _value_i11 h_2916)))))
    exact (((by
      let _equal_wd_1_0 := _object_w8
      let _equal_wd_1_1 := _object_w9
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
      let _equal_wd_1_0 := _object_w10
      let _equal_wd_1_1 := _object_w11
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
      let _equal_wd_1_0 := _object_w12
      let _equal_wd_1_1 := _object_w13
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
      let _equal_wd_1_0 := _object_w13
      let _equal_wd_1_1 := _object_w14
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
      let _equal_wd_1_0 := _object_w15
      let _equal_wd_1_1 := _object_w16
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
      let _equal_wd_1_0 := _object_w16
      let _equal_wd_1_1 := _object_w17
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
      let _equal_wd_1_0 := _object_w14
      let _equal_wd_1_1 := _object_w17
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
      let _equal_wd_1_0 := _object_w12
      let _equal_wd_1_1 := _object_w15
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
  ) := (by
    intro _Host_i9 _rep_i9 _value_i9 h_2914 _Host_i10 _rep_i10 _value_i10 h_2915 _Host_i11 _rep_i11 _value_i11 h_2916
    let _object_w8 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_2930 h_2931 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_2930)
      have h_2930 : Litex.In _value_i7 (Litex.Z (M := M)) := h_2930
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_2931)
      have h_2931 : Litex.In _value_i8 (Litex.Z (M := M)) := h_2931
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2930) (Litex.integerToComplex _value_i8 h_2931))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2930) (Litex.integerToComplex _value_i8 h_2931))
        exact (Litex.addInZ _value_i7 _value_i8 h_2930 h_2931))));
    let _wd_2_1 := _value_i9;
    let _wd_2_2 := _value_i10;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 h_2915 True.intro))
    let _object_w9 := (Litex.add _value_i9 _value_i10 (Litex.integerToComplex _value_i9 h_2914) (Litex.integerToComplex _value_i10 h_2915))
    have h_2893 : (by
      let _equal_wd_1_0 := _object_w8
      let _equal_wd_1_1 := _object_w9
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) from by
              let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                intro _raw_i7 _raw_i8 h_3885 h_3886 _
                let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_3885)
                have h_3885 : Litex.In _value_i7 (Litex.Z (M := M)) := h_3885
                let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_3886)
                have h_3886 : Litex.In _value_i8 (Litex.Z (M := M)) := h_3886
                change (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_3885) (Litex.integerToComplex _value_i8 h_3886))
                  exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_3885) (Litex.integerToComplex _value_i8 h_3886))
                  exact (Litex.addInZ _value_i7 _value_i8 h_3885 h_3886))));
              let _wd_2_1 := _value_i9;
              let _wd_2_2 := _value_i10;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 h_2915 True.intro))
              let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                intro _raw_i7 _raw_i8 h_4072 h_4073 _
                let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_4072)
                have h_4072 : Litex.In _value_i7 (Litex.Z (M := M)) := h_4072
                let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4073)
                have h_4073 : Litex.In _value_i8 (Litex.Z (M := M)) := h_4073
                change (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_4072) (Litex.integerToComplex _value_i8 h_4073))
                  exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_4072) (Litex.integerToComplex _value_i8 h_4073))
                  exact (Litex.addInZ _value_i7 _value_i8 h_4072 h_4073))));
              let _wd_2_1 := _value_i9;
              let _wd_2_2 := _value_i10;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 h_2915 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) from rfl))
            ))).trans _litex_residual)
          )
      )
    let _object_w10 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_4358 h_4359 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_4358)
      have h_4358 : Litex.In _value_i7 (Litex.Z (M := M)) := h_4358
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4359)
      have h_4359 : Litex.In _value_i8 (Litex.Z (M := M)) := h_4359
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_4358) (Litex.integerToComplex _value_i8 h_4359))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_4358) (Litex.integerToComplex _value_i8 h_4359))
        exact (Litex.addInZ _value_i7 _value_i8 h_4358 h_4359))));
    let _wd_2_1 := _value_i10;
    let _wd_2_2 := _value_i11;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2915 h_2916 True.intro))
    let _object_w11 := (Litex.add _value_i10 _value_i11 (Litex.integerToComplex _value_i10 h_2915) (Litex.integerToComplex _value_i11 h_2916))
    have h_2894 : (by
      let _equal_wd_1_0 := _object_w10
      let _equal_wd_1_1 := _object_w11
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
              let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                intro _raw_i7 _raw_i8 h_5333 h_5334 _
                let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_5333)
                have h_5333 : Litex.In _value_i7 (Litex.Z (M := M)) := h_5333
                let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_5334)
                have h_5334 : Litex.In _value_i8 (Litex.Z (M := M)) := h_5334
                change (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5333) (Litex.integerToComplex _value_i8 h_5334))
                  exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5333) (Litex.integerToComplex _value_i8 h_5334))
                  exact (Litex.addInZ _value_i7 _value_i8 h_5333 h_5334))));
              let _wd_2_1 := _value_i10;
              let _wd_2_2 := _value_i11;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2915 h_2916 True.intro))
              let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                intro _raw_i7 _raw_i8 h_5524 h_5525 _
                let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_5524)
                have h_5524 : Litex.In _value_i7 (Litex.Z (M := M)) := h_5524
                let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_5525)
                have h_5525 : Litex.In _value_i8 (Litex.Z (M := M)) := h_5525
                change (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5524) (Litex.integerToComplex _value_i8 h_5525))
                  exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5524) (Litex.integerToComplex _value_i8 h_5525))
                  exact (Litex.addInZ _value_i7 _value_i8 h_5524 h_5525))));
              let _wd_2_1 := _value_i10;
              let _wd_2_2 := _value_i11;
              (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2915 h_2916 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from rfl))
            ))).trans _litex_residual)
          )
      )
    let _object_w12 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_5814 h_5815 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_5814)
      have h_5814 : Litex.In _value_i7 (Litex.Z (M := M)) := h_5814
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_5815)
      have h_5815 : Litex.In _value_i8 (Litex.Z (M := M)) := h_5815
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5814) (Litex.integerToComplex _value_i8 h_5815))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5814) (Litex.integerToComplex _value_i8 h_5815))
        exact (Litex.addInZ _value_i7 _value_i8 h_5814 h_5815))));
    let _wd_2_1 := _object_w8;
    let _wd_2_2 := _value_i11;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
      let _atomic_wd_1_0 := _object_w8
      exact (Litex.inOfSame _object_w8 _object_w8 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w8) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w8))) h_2916 True.intro))
    let _object_w13 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_6046 h_6047 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_6046)
      have h_6046 : Litex.In _value_i7 (Litex.Z (M := M)) := h_6046
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_6047)
      have h_6047 : Litex.In _value_i8 (Litex.Z (M := M)) := h_6047
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6046) (Litex.integerToComplex _value_i8 h_6047))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6046) (Litex.integerToComplex _value_i8 h_6047))
        exact (Litex.addInZ _value_i7 _value_i8 h_6046 h_6047))));
    let _wd_2_1 := _object_w9;
    let _wd_2_2 := _value_i11;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
      let _atomic_wd_1_0 := _object_w9
      exact (Litex.addInZ _value_i9 _value_i10 h_2914 h_2915)) h_2916 True.intro))
    have h_2895 : (by
      let _equal_wd_1_0 := _object_w12
      let _equal_wd_1_1 := _object_w13
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_2893 (show @Eq M.Value _ _ from Eq.refl _)))
          )
      )
    let _object_w14 := (let _wd_2_0 := _object_w9;
    let _wd_2_1 := _value_i11;
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_1_0 := _object_w9
      exact (Litex.addInC _value_i9 _value_i10 (Litex.integerToComplex _value_i9 h_2914) (Litex.integerToComplex _value_i10 h_2915))) (Litex.integerToComplex _wd_2_1 h_2916)))
    have h_2896 : (by
      let _equal_wd_1_0 := _object_w13
      let _equal_wd_1_1 := _object_w14
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)), (Litex.denote _value_i11)])) = (M.addValue (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) (Litex.denote _value_i11)) from by
              have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) (Litex.denote _value_i11)) = (M.addValue (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) (Litex.denote _value_i11)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)), (Litex.denote _value_i11)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)), (Litex.denote _value_i11)])) = (M.addValue (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) (Litex.denote _value_i11)) from by
              let _litex_original := _object_w13
              let _litex_literal := _object_w13
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) (Litex.denote _value_i11)) from rfl))
            ))).trans _litex_residual)
          )
      )
    let _object_w15 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_6892 h_6893 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_6892)
      have h_6892 : Litex.In _value_i7 (Litex.Z (M := M)) := h_6892
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_6893)
      have h_6893 : Litex.In _value_i8 (Litex.Z (M := M)) := h_6893
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6892) (Litex.integerToComplex _value_i8 h_6893))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6892) (Litex.integerToComplex _value_i8 h_6893))
        exact (Litex.addInZ _value_i7 _value_i8 h_6892 h_6893))));
    let _wd_2_1 := _value_i9;
    let _wd_2_2 := _object_w10;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 (by
      let _atomic_wd_1_0 := _object_w10
      exact (Litex.inOfSame _object_w10 _object_w10 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w10) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w10))) True.intro))
    let _object_w16 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
      intro _raw_i7 _raw_i8 h_7120 h_7121 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_7120)
      have h_7120 : Litex.In _value_i7 (Litex.Z (M := M)) := h_7120
      let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_7121)
      have h_7121 : Litex.In _value_i8 (Litex.Z (M := M)) := h_7121
      change (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_7120) (Litex.integerToComplex _value_i8 h_7121))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_7120) (Litex.integerToComplex _value_i8 h_7121))
        exact (Litex.addInZ _value_i7 _value_i8 h_7120 h_7121))));
    let _wd_2_1 := _value_i9;
    let _wd_2_2 := _object_w11;
    (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 (by
      let _atomic_wd_1_0 := _object_w11
      exact (Litex.addInZ _value_i10 _value_i11 h_2915 h_2916)) True.intro))
    have h_2897 : (by
      let _equal_wd_1_0 := _object_w15
      let _equal_wd_1_1 := _object_w16
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_2894))
          )
      )
    let _object_w17 := (let _wd_2_0 := _value_i9;
    let _wd_2_1 := _object_w11;
    (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_2914) (by
      let _atomic_wd_1_0 := _object_w11
      exact (Litex.addInC _value_i10 _value_i11 (Litex.integerToComplex _value_i10 h_2915) (Litex.integerToComplex _value_i11 h_2916)))))
    have h_2898 : (by
      let _equal_wd_1_0 := _object_w16
      let _equal_wd_1_1 := _object_w17
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))])) = (M.addValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))) = (M.addValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))])) = (M.addValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))) from by
              let _litex_original := _object_w16
              let _litex_literal := _object_w16
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))) from rfl))
            ))).trans _litex_residual)
          )
      )
    have h_2899 : (by
      let _equal_wd_1_0 := _object_w14
      let _equal_wd_1_1 := _object_w17
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i9 (Litex.integerToComplex _value_i9 h_2914)) + (Litex.NativeBridge.asComplex _value_i10 (Litex.integerToComplex _value_i10 h_2915))) + (Litex.NativeBridge.asComplex _value_i11 (Litex.integerToComplex _value_i11 h_2916))) ((Litex.NativeBridge.asComplex _value_i9 (Litex.integerToComplex _value_i9 h_2914)) + ((Litex.NativeBridge.asComplex _value_i10 (Litex.integerToComplex _value_i10 h_2915)) + (Litex.NativeBridge.asComplex _value_i11 (Litex.integerToComplex _value_i11 h_2916)))) (Litex.NativeBridge.denoteAdd (_object_w14).val.left _value_i11 (_object_w14).wd.1 (_object_w14).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i9 _value_i10 (_object_w9).wd.1 (_object_w9).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.integerToComplex _value_i9 h_2914)) (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.integerToComplex _value_i10 h_2915))) (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.integerToComplex _value_i11 h_2916))) (Litex.NativeBridge.denoteAdd _value_i9 (_object_w17).val.right (_object_w17).wd.1 (_object_w17).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.integerToComplex _value_i9 h_2914)) (Litex.NativeBridge.denoteAdd _value_i10 _value_i11 (_object_w11).wd.1 (_object_w11).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.integerToComplex _value_i10 h_2915)) (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.integerToComplex _value_i11 h_2916)))) (by ring!))
          )
      )
    have h_2900 : (by
      let _equal_wd_1_0 := _object_w12
      let _equal_wd_1_1 := _object_w15
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            ((((((((h_2895).trans h_2896)).trans h_2899)).trans (h_2898).symm)).trans (h_2897).symm)
          )
      )
    exact (And.intro h_2893 (And.intro h_2894 (And.intro h_2895 (And.intro h_2896 (And.intro h_2897 (And.intro h_2898 (And.intro h_2899 h_2900)))))))
  );
  let h_7956 : (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact (by
      let _set := _atomic_wd_1_0
      exact (Litex.emptySubset (Litex.Z (M := M)))));
  Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True)) h_335 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_336 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i6 : M.Value) => True) i).mpr ⟨h_7956 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_345 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_2901 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))
  exact (by
    let _equal_wd_1_0 := _object_w18
    exact Litex.Same _equal_wd_1_0 _value_i5)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_199
          let _object_w18 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0);
          let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => _raw_i6) (by
            intro _raw_i6 h_213 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_213)
            have h_213 : Litex.In _value_i6 (Litex.Z (M := M)) := h_213
            change Litex.In _value_i6 (Litex.Z (M := M))
            exact h_213));
          let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
            intro _raw_i7 _raw_i8 h_232 h_233 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_232)
            have h_232 : Litex.In _value_i7 (Litex.Z (M := M)) := h_232
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_233)
            have h_233 : Litex.In _value_i8 (Litex.Z (M := M)) := h_233
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_232) (Litex.integerToComplex _value_i8 h_233))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_232) (Litex.integerToComplex _value_i8 h_233))
              exact (Litex.addInZ _value_i7 _value_i8 h_232 h_233))));
          let _wd_1_3 := _value_i5;
          (let h_335 : (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact (let _finite_tail_0 := _atomic_wd_1_0;
            have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
            _finite_0));
          let h_336 : Litex.In _wd_1_3 (Litex.Z (M := M)) := h_199;
          let h_345 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_358 : Litex.In _value_i9 (Litex.Z (M := M))) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_359 : Litex.In _value_i10 (Litex.Z (M := M))), (by
            let _object_w4 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_373 h_374 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_373)
              have h_373 : Litex.In _value_i7 (Litex.Z (M := M)) := h_373
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_374)
              have h_374 : Litex.In _value_i8 (Litex.Z (M := M)) := h_374
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_373) (Litex.integerToComplex _value_i8 h_374))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_373) (Litex.integerToComplex _value_i8 h_374))
                exact (Litex.addInZ _value_i7 _value_i8 h_373 h_374))));
            let _wd_2_1 := _value_i9;
            let _wd_2_2 := _value_i10;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_358 h_359 True.intro))
            let _object_w5 := (Litex.add _value_i9 _value_i10 (Litex.integerToComplex _value_i9 h_358) (Litex.integerToComplex _value_i10 h_359))
            let _object_w6 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_1637 h_1638 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1637)
              have h_1637 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1637
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1638)
              have h_1638 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1638
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1637) (Litex.integerToComplex _value_i8 h_1638))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1637) (Litex.integerToComplex _value_i8 h_1638))
                exact (Litex.addInZ _value_i7 _value_i8 h_1637 h_1638))));
            let _wd_2_1 := _value_i10;
            let _wd_2_2 := _value_i9;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_359 h_358 True.intro))
            let _object_w7 := (Litex.add _value_i10 _value_i9 (Litex.integerToComplex _value_i10 h_359) (Litex.integerToComplex _value_i9 h_358))
            exact (((by
              let _equal_wd_1_0 := _object_w4
              let _equal_wd_1_1 := _object_w5
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w6
              let _equal_wd_1_1 := _object_w7
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w5
              let _equal_wd_1_1 := _object_w7
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _object_w4
              let _equal_wd_1_1 := _object_w6
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
          ) := (by
            intro _Host_i9 _rep_i9 _value_i9 h_358 _Host_i10 _rep_i10 _value_i10 h_359
            let _object_w4 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_373 h_374 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_373)
              have h_373 : Litex.In _value_i7 (Litex.Z (M := M)) := h_373
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_374)
              have h_374 : Litex.In _value_i8 (Litex.Z (M := M)) := h_374
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_373) (Litex.integerToComplex _value_i8 h_374))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_373) (Litex.integerToComplex _value_i8 h_374))
                exact (Litex.addInZ _value_i7 _value_i8 h_373 h_374))));
            let _wd_2_1 := _value_i9;
            let _wd_2_2 := _value_i10;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_358 h_359 True.intro))
            let _object_w5 := (Litex.add _value_i9 _value_i10 (Litex.integerToComplex _value_i9 h_358) (Litex.integerToComplex _value_i10 h_359))
            have h_341 : (by
              let _equal_wd_1_0 := _object_w4
              let _equal_wd_1_1 := _object_w5
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) from by
                      let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                        intro _raw_i7 _raw_i8 h_1220 h_1221 _
                        let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1220)
                        have h_1220 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1220
                        let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1221)
                        have h_1221 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1221
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1220) (Litex.integerToComplex _value_i8 h_1221))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1220) (Litex.integerToComplex _value_i8 h_1221))
                          exact (Litex.addInZ _value_i7 _value_i8 h_1220 h_1221))));
                      let _wd_2_1 := _value_i9;
                      let _wd_2_2 := _value_i10;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_358 h_359 True.intro))
                      let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                        intro _raw_i7 _raw_i8 h_1387 h_1388 _
                        let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1387)
                        have h_1387 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1387
                        let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1388)
                        have h_1388 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1388
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1387) (Litex.integerToComplex _value_i8 h_1388))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1387) (Litex.integerToComplex _value_i8 h_1388))
                          exact (Litex.addInZ _value_i7 _value_i8 h_1387 h_1388))));
                      let _wd_2_1 := _value_i9;
                      let _wd_2_2 := _value_i10;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_358 h_359 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            let _object_w6 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_1637 h_1638 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1637)
              have h_1637 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1637
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1638)
              have h_1638 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1638
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1637) (Litex.integerToComplex _value_i8 h_1638))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_1637) (Litex.integerToComplex _value_i8 h_1638))
                exact (Litex.addInZ _value_i7 _value_i8 h_1637 h_1638))));
            let _wd_2_1 := _value_i10;
            let _wd_2_2 := _value_i9;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_359 h_358 True.intro))
            let _object_w7 := (Litex.add _value_i10 _value_i9 (Litex.integerToComplex _value_i10 h_359) (Litex.integerToComplex _value_i9 h_358))
            have h_342 : (by
              let _equal_wd_1_0 := _object_w6
              let _equal_wd_1_1 := _object_w7
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i9)])) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i9)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i9)) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i9)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i9)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i9)])) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i9)) from by
                      let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                        intro _raw_i7 _raw_i8 h_2484 h_2485 _
                        let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_2484)
                        have h_2484 : Litex.In _value_i7 (Litex.Z (M := M)) := h_2484
                        let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_2485)
                        have h_2485 : Litex.In _value_i8 (Litex.Z (M := M)) := h_2485
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2484) (Litex.integerToComplex _value_i8 h_2485))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2484) (Litex.integerToComplex _value_i8 h_2485))
                          exact (Litex.addInZ _value_i7 _value_i8 h_2484 h_2485))));
                      let _wd_2_1 := _value_i10;
                      let _wd_2_2 := _value_i9;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_359 h_358 True.intro))
                      let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                        intro _raw_i7 _raw_i8 h_2651 h_2652 _
                        let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_2651)
                        have h_2651 : Litex.In _value_i7 (Litex.Z (M := M)) := h_2651
                        let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_2652)
                        have h_2652 : Litex.In _value_i8 (Litex.Z (M := M)) := h_2652
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2651) (Litex.integerToComplex _value_i8 h_2652))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2651) (Litex.integerToComplex _value_i8 h_2652))
                          exact (Litex.addInZ _value_i7 _value_i8 h_2651 h_2652))));
                      let _wd_2_1 := _value_i10;
                      let _wd_2_2 := _value_i9;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_359 h_358 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i9)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            have h_343 : (by
              let _equal_wd_1_0 := _object_w5
              let _equal_wd_1_1 := _object_w7
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i9 (Litex.integerToComplex _value_i9 h_358)) + (Litex.NativeBridge.asComplex _value_i10 (Litex.integerToComplex _value_i10 h_359))) ((Litex.NativeBridge.asComplex _value_i10 (Litex.integerToComplex _value_i10 h_359)) + (Litex.NativeBridge.asComplex _value_i9 (Litex.integerToComplex _value_i9 h_358))) (Litex.NativeBridge.denoteAdd _value_i9 _value_i10 (_object_w5).wd.1 (_object_w5).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.integerToComplex _value_i9 h_358)) (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.integerToComplex _value_i10 h_359))) (Litex.NativeBridge.denoteAdd _value_i10 _value_i9 (_object_w7).wd.1 (_object_w7).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.integerToComplex _value_i10 h_359)) (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.integerToComplex _value_i9 h_358))) (by ring!))
                  )
              )
            have h_344 : (by
              let _equal_wd_1_0 := _object_w4
              let _equal_wd_1_1 := _object_w6
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    ((((h_341).trans h_343)).trans (h_342).symm)
                  )
              )
            exact (And.intro h_341 (And.intro h_342 (And.intro h_343 h_344)))
          );
          let h_2901 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_2914 : Litex.In _value_i9 (Litex.Z (M := M))) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_2915 : Litex.In _value_i10 (Litex.Z (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_2916 : Litex.In _value_i11 (Litex.Z (M := M))), (by
            let _object_w8 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_2930 h_2931 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_2930)
              have h_2930 : Litex.In _value_i7 (Litex.Z (M := M)) := h_2930
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_2931)
              have h_2931 : Litex.In _value_i8 (Litex.Z (M := M)) := h_2931
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2930) (Litex.integerToComplex _value_i8 h_2931))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2930) (Litex.integerToComplex _value_i8 h_2931))
                exact (Litex.addInZ _value_i7 _value_i8 h_2930 h_2931))));
            let _wd_2_1 := _value_i9;
            let _wd_2_2 := _value_i10;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 h_2915 True.intro))
            let _object_w9 := (Litex.add _value_i9 _value_i10 (Litex.integerToComplex _value_i9 h_2914) (Litex.integerToComplex _value_i10 h_2915))
            let _object_w10 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_4358 h_4359 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_4358)
              have h_4358 : Litex.In _value_i7 (Litex.Z (M := M)) := h_4358
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4359)
              have h_4359 : Litex.In _value_i8 (Litex.Z (M := M)) := h_4359
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_4358) (Litex.integerToComplex _value_i8 h_4359))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_4358) (Litex.integerToComplex _value_i8 h_4359))
                exact (Litex.addInZ _value_i7 _value_i8 h_4358 h_4359))));
            let _wd_2_1 := _value_i10;
            let _wd_2_2 := _value_i11;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2915 h_2916 True.intro))
            let _object_w11 := (Litex.add _value_i10 _value_i11 (Litex.integerToComplex _value_i10 h_2915) (Litex.integerToComplex _value_i11 h_2916))
            let _object_w12 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_5814 h_5815 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_5814)
              have h_5814 : Litex.In _value_i7 (Litex.Z (M := M)) := h_5814
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_5815)
              have h_5815 : Litex.In _value_i8 (Litex.Z (M := M)) := h_5815
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5814) (Litex.integerToComplex _value_i8 h_5815))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5814) (Litex.integerToComplex _value_i8 h_5815))
                exact (Litex.addInZ _value_i7 _value_i8 h_5814 h_5815))));
            let _wd_2_1 := _object_w8;
            let _wd_2_2 := _value_i11;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
              let _atomic_wd_1_0 := _object_w8
              exact (Litex.inOfSame _object_w8 _object_w8 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w8) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w8))) h_2916 True.intro))
            let _object_w13 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_6046 h_6047 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_6046)
              have h_6046 : Litex.In _value_i7 (Litex.Z (M := M)) := h_6046
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_6047)
              have h_6047 : Litex.In _value_i8 (Litex.Z (M := M)) := h_6047
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6046) (Litex.integerToComplex _value_i8 h_6047))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6046) (Litex.integerToComplex _value_i8 h_6047))
                exact (Litex.addInZ _value_i7 _value_i8 h_6046 h_6047))));
            let _wd_2_1 := _object_w9;
            let _wd_2_2 := _value_i11;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
              let _atomic_wd_1_0 := _object_w9
              exact (Litex.addInZ _value_i9 _value_i10 h_2914 h_2915)) h_2916 True.intro))
            let _object_w14 := (let _wd_2_0 := _object_w9;
            let _wd_2_1 := _value_i11;
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _object_w9
              exact (Litex.addInC _value_i9 _value_i10 (Litex.integerToComplex _value_i9 h_2914) (Litex.integerToComplex _value_i10 h_2915))) (Litex.integerToComplex _wd_2_1 h_2916)))
            let _object_w15 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_6892 h_6893 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_6892)
              have h_6892 : Litex.In _value_i7 (Litex.Z (M := M)) := h_6892
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_6893)
              have h_6893 : Litex.In _value_i8 (Litex.Z (M := M)) := h_6893
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6892) (Litex.integerToComplex _value_i8 h_6893))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6892) (Litex.integerToComplex _value_i8 h_6893))
                exact (Litex.addInZ _value_i7 _value_i8 h_6892 h_6893))));
            let _wd_2_1 := _value_i9;
            let _wd_2_2 := _object_w10;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 (by
              let _atomic_wd_1_0 := _object_w10
              exact (Litex.inOfSame _object_w10 _object_w10 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w10) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w10))) True.intro))
            let _object_w16 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_7120 h_7121 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_7120)
              have h_7120 : Litex.In _value_i7 (Litex.Z (M := M)) := h_7120
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_7121)
              have h_7121 : Litex.In _value_i8 (Litex.Z (M := M)) := h_7121
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_7120) (Litex.integerToComplex _value_i8 h_7121))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_7120) (Litex.integerToComplex _value_i8 h_7121))
                exact (Litex.addInZ _value_i7 _value_i8 h_7120 h_7121))));
            let _wd_2_1 := _value_i9;
            let _wd_2_2 := _object_w11;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 (by
              let _atomic_wd_1_0 := _object_w11
              exact (Litex.addInZ _value_i10 _value_i11 h_2915 h_2916)) True.intro))
            let _object_w17 := (let _wd_2_0 := _value_i9;
            let _wd_2_1 := _object_w11;
            (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_2914) (by
              let _atomic_wd_1_0 := _object_w11
              exact (Litex.addInC _value_i10 _value_i11 (Litex.integerToComplex _value_i10 h_2915) (Litex.integerToComplex _value_i11 h_2916)))))
            exact (((by
              let _equal_wd_1_0 := _object_w8
              let _equal_wd_1_1 := _object_w9
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w10
              let _equal_wd_1_1 := _object_w11
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w12
              let _equal_wd_1_1 := _object_w13
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w13
              let _equal_wd_1_1 := _object_w14
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w15
              let _equal_wd_1_1 := _object_w16
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w16
              let _equal_wd_1_1 := _object_w17
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w14
              let _equal_wd_1_1 := _object_w17
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _object_w12
              let _equal_wd_1_1 := _object_w15
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
          ) := (by
            intro _Host_i9 _rep_i9 _value_i9 h_2914 _Host_i10 _rep_i10 _value_i10 h_2915 _Host_i11 _rep_i11 _value_i11 h_2916
            let _object_w8 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_2930 h_2931 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_2930)
              have h_2930 : Litex.In _value_i7 (Litex.Z (M := M)) := h_2930
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_2931)
              have h_2931 : Litex.In _value_i8 (Litex.Z (M := M)) := h_2931
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2930) (Litex.integerToComplex _value_i8 h_2931))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_2930) (Litex.integerToComplex _value_i8 h_2931))
                exact (Litex.addInZ _value_i7 _value_i8 h_2930 h_2931))));
            let _wd_2_1 := _value_i9;
            let _wd_2_2 := _value_i10;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 h_2915 True.intro))
            let _object_w9 := (Litex.add _value_i9 _value_i10 (Litex.integerToComplex _value_i9 h_2914) (Litex.integerToComplex _value_i10 h_2915))
            have h_2893 : (by
              let _equal_wd_1_0 := _object_w8
              let _equal_wd_1_1 := _object_w9
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (Litex.denote _value_i10)])) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) from by
                      let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                        intro _raw_i7 _raw_i8 h_3885 h_3886 _
                        let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_3885)
                        have h_3885 : Litex.In _value_i7 (Litex.Z (M := M)) := h_3885
                        let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_3886)
                        have h_3886 : Litex.In _value_i8 (Litex.Z (M := M)) := h_3886
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_3885) (Litex.integerToComplex _value_i8 h_3886))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_3885) (Litex.integerToComplex _value_i8 h_3886))
                          exact (Litex.addInZ _value_i7 _value_i8 h_3885 h_3886))));
                      let _wd_2_1 := _value_i9;
                      let _wd_2_2 := _value_i10;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 h_2915 True.intro))
                      let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                        intro _raw_i7 _raw_i8 h_4072 h_4073 _
                        let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_4072)
                        have h_4072 : Litex.In _value_i7 (Litex.Z (M := M)) := h_4072
                        let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4073)
                        have h_4073 : Litex.In _value_i8 (Litex.Z (M := M)) := h_4073
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_4072) (Litex.integerToComplex _value_i8 h_4073))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_4072) (Litex.integerToComplex _value_i8 h_4073))
                          exact (Litex.addInZ _value_i7 _value_i8 h_4072 h_4073))));
                      let _wd_2_1 := _value_i9;
                      let _wd_2_2 := _value_i10;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 h_2915 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            let _object_w10 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_4358 h_4359 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_4358)
              have h_4358 : Litex.In _value_i7 (Litex.Z (M := M)) := h_4358
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4359)
              have h_4359 : Litex.In _value_i8 (Litex.Z (M := M)) := h_4359
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_4358) (Litex.integerToComplex _value_i8 h_4359))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_4358) (Litex.integerToComplex _value_i8 h_4359))
                exact (Litex.addInZ _value_i7 _value_i8 h_4358 h_4359))));
            let _wd_2_1 := _value_i10;
            let _wd_2_2 := _value_i11;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2915 h_2916 True.intro))
            let _object_w11 := (Litex.add _value_i10 _value_i11 (Litex.integerToComplex _value_i10 h_2915) (Litex.integerToComplex _value_i11 h_2916))
            have h_2894 : (by
              let _equal_wd_1_0 := _object_w10
              let _equal_wd_1_1 := _object_w11
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
                      let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                        intro _raw_i7 _raw_i8 h_5333 h_5334 _
                        let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_5333)
                        have h_5333 : Litex.In _value_i7 (Litex.Z (M := M)) := h_5333
                        let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_5334)
                        have h_5334 : Litex.In _value_i8 (Litex.Z (M := M)) := h_5334
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5333) (Litex.integerToComplex _value_i8 h_5334))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5333) (Litex.integerToComplex _value_i8 h_5334))
                          exact (Litex.addInZ _value_i7 _value_i8 h_5333 h_5334))));
                      let _wd_2_1 := _value_i10;
                      let _wd_2_2 := _value_i11;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2915 h_2916 True.intro))
                      let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
                        intro _raw_i7 _raw_i8 h_5524 h_5525 _
                        let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_5524)
                        have h_5524 : Litex.In _value_i7 (Litex.Z (M := M)) := h_5524
                        let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_5525)
                        have h_5525 : Litex.In _value_i8 (Litex.Z (M := M)) := h_5525
                        change (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5524) (Litex.integerToComplex _value_i8 h_5525))
                          exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5524) (Litex.integerToComplex _value_i8 h_5525))
                          exact (Litex.addInZ _value_i7 _value_i8 h_5524 h_5525))));
                      let _wd_2_1 := _value_i10;
                      let _wd_2_2 := _value_i11;
                      (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2915 h_2916 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            let _object_w12 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_5814 h_5815 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_5814)
              have h_5814 : Litex.In _value_i7 (Litex.Z (M := M)) := h_5814
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_5815)
              have h_5815 : Litex.In _value_i8 (Litex.Z (M := M)) := h_5815
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5814) (Litex.integerToComplex _value_i8 h_5815))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_5814) (Litex.integerToComplex _value_i8 h_5815))
                exact (Litex.addInZ _value_i7 _value_i8 h_5814 h_5815))));
            let _wd_2_1 := _object_w8;
            let _wd_2_2 := _value_i11;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
              let _atomic_wd_1_0 := _object_w8
              exact (Litex.inOfSame _object_w8 _object_w8 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w8) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w8))) h_2916 True.intro))
            let _object_w13 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_6046 h_6047 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_6046)
              have h_6046 : Litex.In _value_i7 (Litex.Z (M := M)) := h_6046
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_6047)
              have h_6047 : Litex.In _value_i8 (Litex.Z (M := M)) := h_6047
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6046) (Litex.integerToComplex _value_i8 h_6047))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6046) (Litex.integerToComplex _value_i8 h_6047))
                exact (Litex.addInZ _value_i7 _value_i8 h_6046 h_6047))));
            let _wd_2_1 := _object_w9;
            let _wd_2_2 := _value_i11;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
              let _atomic_wd_1_0 := _object_w9
              exact (Litex.addInZ _value_i9 _value_i10 h_2914 h_2915)) h_2916 True.intro))
            have h_2895 : (by
              let _equal_wd_1_0 := _object_w12
              let _equal_wd_1_1 := _object_w13
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_2893 (show @Eq M.Value _ _ from Eq.refl _)))
                  )
              )
            let _object_w14 := (let _wd_2_0 := _object_w9;
            let _wd_2_1 := _value_i11;
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _object_w9
              exact (Litex.addInC _value_i9 _value_i10 (Litex.integerToComplex _value_i9 h_2914) (Litex.integerToComplex _value_i10 h_2915))) (Litex.integerToComplex _wd_2_1 h_2916)))
            have h_2896 : (by
              let _equal_wd_1_0 := _object_w13
              let _equal_wd_1_1 := _object_w14
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)), (Litex.denote _value_i11)])) = (M.addValue (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) (Litex.denote _value_i11)) from by
                      have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) (Litex.denote _value_i11)) = (M.addValue (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) (Litex.denote _value_i11)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)), (Litex.denote _value_i11)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)), (Litex.denote _value_i11)])) = (M.addValue (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) (Litex.denote _value_i11)) from by
                      let _litex_original := _object_w13
                      let _litex_literal := _object_w13
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i9) (Litex.denote _value_i10)) (Litex.denote _value_i11)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            let _object_w15 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_6892 h_6893 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_6892)
              have h_6892 : Litex.In _value_i7 (Litex.Z (M := M)) := h_6892
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_6893)
              have h_6893 : Litex.In _value_i8 (Litex.Z (M := M)) := h_6893
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6892) (Litex.integerToComplex _value_i8 h_6893))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_6892) (Litex.integerToComplex _value_i8 h_6893))
                exact (Litex.addInZ _value_i7 _value_i8 h_6892 h_6893))));
            let _wd_2_1 := _value_i9;
            let _wd_2_2 := _object_w10;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 (by
              let _atomic_wd_1_0 := _object_w10
              exact (Litex.inOfSame _object_w10 _object_w10 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w10) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w10))) True.intro))
            let _object_w16 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by
              intro _raw_i7 _raw_i8 h_7120 h_7121 _
              let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_7120)
              have h_7120 : Litex.In _value_i7 (Litex.Z (M := M)) := h_7120
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_7121)
              have h_7121 : Litex.In _value_i8 (Litex.Z (M := M)) := h_7121
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_7120) (Litex.integerToComplex _value_i8 h_7121))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i7 _value_i8 (Litex.integerToComplex _value_i7 h_7120) (Litex.integerToComplex _value_i8 h_7121))
                exact (Litex.addInZ _value_i7 _value_i8 h_7120 h_7121))));
            let _wd_2_1 := _value_i9;
            let _wd_2_2 := _object_w11;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2914 (by
              let _atomic_wd_1_0 := _object_w11
              exact (Litex.addInZ _value_i10 _value_i11 h_2915 h_2916)) True.intro))
            have h_2897 : (by
              let _equal_wd_1_0 := _object_w15
              let _equal_wd_1_1 := _object_w16
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_2894))
                  )
              )
            let _object_w17 := (let _wd_2_0 := _value_i9;
            let _wd_2_1 := _object_w11;
            (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_2914) (by
              let _atomic_wd_1_0 := _object_w11
              exact (Litex.addInC _value_i10 _value_i11 (Litex.integerToComplex _value_i10 h_2915) (Litex.integerToComplex _value_i11 h_2916)))))
            have h_2898 : (by
              let _equal_wd_1_0 := _object_w16
              let _equal_wd_1_1 := _object_w17
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))])) = (M.addValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))) = (M.addValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i9), (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))])) = (M.addValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))) from by
                      let _litex_original := _object_w16
                      let _litex_literal := _object_w16
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => (M.addValue _raw_i7 _raw_i8)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i9) (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            have h_2899 : (by
              let _equal_wd_1_0 := _object_w14
              let _equal_wd_1_1 := _object_w17
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i9 (Litex.integerToComplex _value_i9 h_2914)) + (Litex.NativeBridge.asComplex _value_i10 (Litex.integerToComplex _value_i10 h_2915))) + (Litex.NativeBridge.asComplex _value_i11 (Litex.integerToComplex _value_i11 h_2916))) ((Litex.NativeBridge.asComplex _value_i9 (Litex.integerToComplex _value_i9 h_2914)) + ((Litex.NativeBridge.asComplex _value_i10 (Litex.integerToComplex _value_i10 h_2915)) + (Litex.NativeBridge.asComplex _value_i11 (Litex.integerToComplex _value_i11 h_2916)))) (Litex.NativeBridge.denoteAdd (_object_w14).val.left _value_i11 (_object_w14).wd.1 (_object_w14).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i9 _value_i10 (_object_w9).wd.1 (_object_w9).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.integerToComplex _value_i9 h_2914)) (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.integerToComplex _value_i10 h_2915))) (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.integerToComplex _value_i11 h_2916))) (Litex.NativeBridge.denoteAdd _value_i9 (_object_w17).val.right (_object_w17).wd.1 (_object_w17).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i9 (Litex.integerToComplex _value_i9 h_2914)) (Litex.NativeBridge.denoteAdd _value_i10 _value_i11 (_object_w11).wd.1 (_object_w11).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.integerToComplex _value_i10 h_2915)) (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.integerToComplex _value_i11 h_2916)))) (by ring!))
                  )
              )
            have h_2900 : (by
              let _equal_wd_1_0 := _object_w12
              let _equal_wd_1_1 := _object_w15
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    ((((((((h_2895).trans h_2896)).trans h_2899)).trans (h_2898).symm)).trans (h_2897).symm)
                  )
              )
            exact (And.intro h_2893 (And.intro h_2894 (And.intro h_2895 (And.intro h_2896 (And.intro h_2897 (And.intro h_2898 (And.intro h_2899 h_2900)))))))
          );
          let h_7956 : (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact (by
              let _set := _atomic_wd_1_0
              exact (Litex.emptySubset (Litex.Z (M := M)))));
          Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True)) h_335 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_336 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i6 : M.Value) => True) i).mpr ⟨h_7956 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_345 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_2901 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))
          have h_184 : (by
            let _equal_wd_1_0 := _object_w18
            exact Litex.Same _equal_wd_1_0 _value_i5) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w18;
                  (show Litex.Same _equal_wd_1_0 _value_i5 from ((Litex.finiteFoldEmpty _equal_wd_1_0 rfl))))
                )
            )
          exact h_184
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_fold_x5f_empty_x2f_statement_x2e_lit
