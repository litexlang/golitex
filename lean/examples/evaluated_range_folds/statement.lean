import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_range_x5f_folds_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_475 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
  let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
    intro _raw_i1 h_489 _
    let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_489)
    have h_489 : Litex.In _value_i1 (Litex.Z (M := M)) := h_489
    change Litex.In _value_i1 (Litex.Z (M := M))
    exact h_489));
  let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_508 h_509 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_508)
    have h_508 : Litex.In _value_i2 (Litex.Z (M := M)) := h_508
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_509)
    have h_509 : Litex.In _value_i3 (Litex.Z (M := M)) := h_509
    change (by
      let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_508) (Litex.integerToComplex _value_i3 h_509))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_508) (Litex.integerToComplex _value_i3 h_509))
      exact (Litex.subInZ _value_i2 _value_i3 h_508 h_509))));
  let _wd_1_4 := (Litex.number (M := M) (0 : ℂ));
  (let h_591 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
  let h_592 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
  let h_593 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
  Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_591 h_592 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_593 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_489 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_489)
          have h_489 : Litex.In _value_i1 (Litex.Z (M := M)) := h_489
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_489));
        let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
          intro _raw_i2 _raw_i3 h_508 h_509 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_508)
          have h_508 : Litex.In _value_i2 (Litex.Z (M := M)) := h_508
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_509)
          have h_509 : Litex.In _value_i3 (Litex.Z (M := M)) := h_509
          change (by
            let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_508) (Litex.integerToComplex _value_i3 h_509))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_508) (Litex.integerToComplex _value_i3 h_509))
            exact (Litex.subInZ _value_i2 _value_i3 h_508 h_509))));
        let _wd_1_4 := (Litex.number (M := M) (0 : ℂ));
        (let h_591 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
        let h_592 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
        let h_593 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
        Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_591 h_592 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_593 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-6 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-6 : ℂ)) from (((Eq.refl (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_14 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
          have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_14));
        let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
          intro _raw_i2 _raw_i3 h_33 h_34 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_33)
          have h_33 : Litex.In _value_i2 (Litex.Z (M := M)) := h_33
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_34)
          have h_34 : Litex.In _value_i3 (Litex.Z (M := M)) := h_34
          change (by
            let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_33) (Litex.integerToComplex _value_i3 h_34))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_33) (Litex.integerToComplex _value_i3 h_34))
            exact (Litex.subInZ _value_i2 _value_i3 h_33 h_34))));
        let _wd_1_4 := (Litex.number (M := M) (0 : ℂ));
        (let h_116 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
        let h_117 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
        let h_118 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
        Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_116 h_117 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_118 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))))).trans (show (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_14 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
          have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_14));
        let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
          intro _raw_i2 _raw_i3 h_33 h_34 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_33)
          have h_33 : Litex.In _value_i2 (Litex.Z (M := M)) := h_33
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_34)
          have h_34 : Litex.In _value_i3 (Litex.Z (M := M)) := h_34
          change (by
            let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_33) (Litex.integerToComplex _value_i3 h_34))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_33) (Litex.integerToComplex _value_i3 h_34))
            exact (Litex.subInZ _value_i2 _value_i3 h_33 h_34))));
        let _wd_1_4 := (Litex.number (M := M) (0 : ℂ));
        (let h_116 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
        let h_117 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
        let h_118 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
        Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_116 h_117 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_118 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))) = M.number (-6 : ℂ) from (by
          let _fold := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_14 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
            have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_14));
          let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_33 h_34 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_33)
            have h_33 : Litex.In _value_i2 (Litex.Z (M := M)) := h_33
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_34)
            have h_34 : Litex.In _value_i3 (Litex.Z (M := M)) := h_34
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_33) (Litex.integerToComplex _value_i3 h_34))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_33) (Litex.integerToComplex _value_i3 h_34))
              exact (Litex.subInZ _value_i2 _value_i3 h_33 h_34))));
          let _wd_1_4 := (Litex.number (M := M) (0 : ℂ));
          (let h_116 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
          let h_117 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
          let h_118 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
          Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_116 h_117 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_118 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))
          have _seed : Litex.denote _fold.val.seed = M.number (0 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))
          have _term_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (1 : ℂ)) = M.number (1 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_134 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_134)
            have h_134 : Litex.In _value_i1 (Litex.Z (M := M)) := h_134
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_134));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_134 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_134)
            have h_134 : Litex.In _value_i1 (Litex.Z (M := M)) := h_134
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_134))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (1 : ℂ)) := by change (fun (_raw_i1 : M.Value) => _raw_i1) (Litex.denote _call.val.argument) = (M.number (1 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (1 : ℂ)) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (0 : ℂ)) (M.number (1 : ℂ))) = M.number (-1 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_154 h_155 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_154)
            have h_154 : Litex.In _value_i2 (Litex.Z (M := M)) := h_154
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
            have h_155 : Litex.In _value_i3 (Litex.Z (M := M)) := h_155
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_154) (Litex.integerToComplex _value_i3 h_155))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_154) (Litex.integerToComplex _value_i3 h_155))
              exact (Litex.subInZ _value_i2 _value_i3 h_154 h_155))));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_154 h_155 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_154)
            have h_154 : Litex.In _value_i2 (Litex.Z (M := M)) := h_154
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
            have h_155 : Litex.In _value_i3 (Litex.Z (M := M)) := h_155
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_154) (Litex.integerToComplex _value_i3 h_155))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_154) (Litex.integerToComplex _value_i3 h_155))
              exact (Litex.subInZ _value_i2 _value_i3 h_154 h_155))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (0 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) := by change (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) = M.number (-1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _term_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (2 : ℂ)) = M.number (2 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_252 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_252)
            have h_252 : Litex.In _value_i1 (Litex.Z (M := M)) := h_252
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_252));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_252 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_252)
            have h_252 : Litex.In _value_i1 (Litex.Z (M := M)) := h_252
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_252))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := by change (fun (_raw_i1 : M.Value) => _raw_i1) (Litex.denote _call.val.argument) = (M.number (2 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (-1 : ℂ)) (M.number (2 : ℂ))) = M.number (-3 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_272 h_273 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_272)
            have h_272 : Litex.In _value_i2 (Litex.Z (M := M)) := h_272
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_273)
            have h_273 : Litex.In _value_i3 (Litex.Z (M := M)) := h_273
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_272) (Litex.integerToComplex _value_i3 h_273))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_272) (Litex.integerToComplex _value_i3 h_273))
              exact (Litex.subInZ _value_i2 _value_i3 h_272 h_273))));
          let _wd_1_1 := (Litex.number (M := M) (-1 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-1 : ℂ) (-1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_272 h_273 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_272)
            have h_272 : Litex.In _value_i2 (Litex.Z (M := M)) := h_272
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_273)
            have h_273 : Litex.In _value_i3 (Litex.Z (M := M)) := h_273
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_272) (Litex.integerToComplex _value_i3 h_273))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_272) (Litex.integerToComplex _value_i3 h_273))
              exact (Litex.subInZ _value_i2 _value_i3 h_272 h_273))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (-1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num : (-1 : ℂ) = (-1 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))) := by change (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))) = M.number (-3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _term_2 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (3 : ℂ)) = M.number (3 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_370 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_370)
            have h_370 : Litex.In _value_i1 (Litex.Z (M := M)) := h_370
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_370));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_370 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_370)
            have h_370 : Litex.In _value_i1 (Litex.Z (M := M)) := h_370
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_370))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := by change (fun (_raw_i1 : M.Value) => _raw_i1) (Litex.denote _call.val.argument) = (M.number (3 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_2 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (-3 : ℂ)) (M.number (3 : ℂ))) = M.number (-6 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_390 h_391 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_390)
            have h_390 : Litex.In _value_i2 (Litex.Z (M := M)) := h_390
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_391)
            have h_391 : Litex.In _value_i3 (Litex.Z (M := M)) := h_391
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_390) (Litex.integerToComplex _value_i3 h_391))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_390) (Litex.integerToComplex _value_i3 h_391))
              exact (Litex.subInZ _value_i2 _value_i3 h_390 h_391))));
          let _wd_1_1 := (Litex.number (M := M) (-3 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-3 : ℂ) (-3 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_390 h_391 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_390)
            have h_390 : Litex.In _value_i2 (Litex.Z (M := M)) := h_390
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_391)
            have h_391 : Litex.In _value_i3 (Litex.Z (M := M)) := h_391
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_390) (Litex.integerToComplex _value_i3 h_391))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_390) (Litex.integerToComplex _value_i3 h_391))
              exact (Litex.subInZ _value_i2 _value_i3 h_390 h_391))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (-3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))) := by change (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))) = M.number (-6 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          apply Litex.rangeFoldDenote _fold (1 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (M.number (-6 : ℂ))
          have _indices : Litex.integerFoldIndices (1 : ℤ) (3 : ℤ) = [(1 : ℤ), (2 : ℤ), (3 : ℤ)] := by decide
          norm_num [Litex.foldValue, Litex.foldApply2, _indices, _seed, _term_0, _step_0, _term_1, _step_1, _term_2, _step_2]))).trans (((Litex.NativeBridge.denoteNumber (M := M) (-6 : ℂ))).trans (congrArg M.number (by norm_num : (-6 : ℂ) = (-6 : ℂ)))).symm)))
      )
  )

noncomputable def _object_w21 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
  intro _raw_i4 h_610 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_610)
  have h_610 : Litex.In _value_i4 (Litex.Z (M := M)) := h_610
  change Litex.In _value_i4 (Litex.Z (M := M))
  exact h_610));
let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.subValue _raw_i5 _raw_i6)) (by
  intro _raw_i5 _raw_i6 h_629 h_630 _
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_629)
  have h_629 : Litex.In _value_i5 (Litex.Z (M := M)) := h_629
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_630)
  have h_630 : Litex.In _value_i6 (Litex.Z (M := M)) := h_630
  change (by
    let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_629) (Litex.integerToComplex _value_i6 h_630))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_629) (Litex.integerToComplex _value_i6 h_630))
    exact (Litex.subInZ _value_i5 _value_i6 h_629 h_630))));
let _wd_1_4 := (Litex.number (M := M) (0 : ℂ));
(let h_712 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
let h_713 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
let h_714 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True)) h_712 h_713 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_714 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i4 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))

theorem h_596 : (by
  let _equal_wd_1_0 := (_object_w21 (M := M))
  let _equal_wd_1_1 := (Litex.number (M := M) (-6 : ℂ))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w21 (M := M));
        let _equal_wd_1_1 := (Litex.number (M := M) (-6 : ℂ));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((show (Litex.denote _equal_wd_1_0) = M.number (-6 : ℂ) from (by
          let _fold := _equal_wd_1_0
          have _seed : Litex.denote _fold.val.seed = M.number (0 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))
          have _term_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (1 : ℂ)) = M.number (1 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
            intro _raw_i4 h_721 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_721)
            have h_721 : Litex.In _value_i4 (Litex.Z (M := M)) := h_721
            change Litex.In _value_i4 (Litex.Z (M := M))
            exact h_721));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (1 : ℂ)) := by change (fun (_raw_i4 : M.Value) => _raw_i4) (Litex.denote _call.val.argument) = (M.number (1 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (1 : ℂ)) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (0 : ℂ)) (M.number (1 : ℂ))) = M.number (-1 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.subValue _raw_i5 _raw_i6)) (by
            intro _raw_i5 _raw_i6 h_730 h_731 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_730)
            have h_730 : Litex.In _value_i5 (Litex.Z (M := M)) := h_730
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_731)
            have h_731 : Litex.In _value_i6 (Litex.Z (M := M)) := h_731
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_730) (Litex.integerToComplex _value_i6 h_731))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_730) (Litex.integerToComplex _value_i6 h_731))
              exact (Litex.subInZ _value_i5 _value_i6 h_730 h_731))));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.operation
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (0 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) := by change (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.subValue _raw_i5 _raw_i6)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) = M.number (-1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _term_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (2 : ℂ)) = M.number (2 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
            intro _raw_i4 h_817 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_817)
            have h_817 : Litex.In _value_i4 (Litex.Z (M := M)) := h_817
            change Litex.In _value_i4 (Litex.Z (M := M))
            exact h_817));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := by change (fun (_raw_i4 : M.Value) => _raw_i4) (Litex.denote _call.val.argument) = (M.number (2 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (-1 : ℂ)) (M.number (2 : ℂ))) = M.number (-3 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.subValue _raw_i5 _raw_i6)) (by
            intro _raw_i5 _raw_i6 h_826 h_827 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_826)
            have h_826 : Litex.In _value_i5 (Litex.Z (M := M)) := h_826
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_827)
            have h_827 : Litex.In _value_i6 (Litex.Z (M := M)) := h_827
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_826) (Litex.integerToComplex _value_i6 h_827))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_826) (Litex.integerToComplex _value_i6 h_827))
              exact (Litex.subInZ _value_i5 _value_i6 h_826 h_827))));
          let _wd_1_1 := (Litex.number (M := M) (-1 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-1 : ℂ) (-1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.operation
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (-1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num : (-1 : ℂ) = (-1 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))) := by change (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.subValue _raw_i5 _raw_i6)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))) = M.number (-3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _term_2 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (3 : ℂ)) = M.number (3 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
            intro _raw_i4 h_913 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_913)
            have h_913 : Litex.In _value_i4 (Litex.Z (M := M)) := h_913
            change Litex.In _value_i4 (Litex.Z (M := M))
            exact h_913));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := by change (fun (_raw_i4 : M.Value) => _raw_i4) (Litex.denote _call.val.argument) = (M.number (3 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_2 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (-3 : ℂ)) (M.number (3 : ℂ))) = M.number (-6 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.subValue _raw_i5 _raw_i6)) (by
            intro _raw_i5 _raw_i6 h_922 h_923 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_922)
            have h_922 : Litex.In _value_i5 (Litex.Z (M := M)) := h_922
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_923)
            have h_923 : Litex.In _value_i6 (Litex.Z (M := M)) := h_923
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_922) (Litex.integerToComplex _value_i6 h_923))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_922) (Litex.integerToComplex _value_i6 h_923))
              exact (Litex.subInZ _value_i5 _value_i6 h_922 h_923))));
          let _wd_1_1 := (Litex.number (M := M) (-3 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-3 : ℂ) (-3 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.operation
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (-3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))) := by change (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.subValue _raw_i5 _raw_i6)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))) = M.number (-6 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          apply Litex.rangeFoldDenote _fold (1 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (M.number (-6 : ℂ))
          have _indices : Litex.integerFoldIndices (1 : ℤ) (3 : ℤ) = [(1 : ℤ), (2 : ℤ), (3 : ℤ)] := by decide
          norm_num [Litex.foldValue, Litex.foldApply2, _indices, _seed, _term_0, _step_0, _term_1, _step_1, _term_2, _step_2]))).trans (((Litex.NativeBridge.denoteNumber (M := M) (-6 : ℂ))).trans (congrArg M.number (by norm_num : (-6 : ℂ) = (-6 : ℂ)))).symm)))
      )
  )

theorem h_1129 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
    intro _raw_i7 h_1143 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1143)
    have h_1143 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1143
    change Litex.In _value_i7 (Litex.Z (M := M))
    exact h_1143));
  let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.subValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_1162 h_1163 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1162)
    have h_1162 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1162
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1163)
    have h_1163 : Litex.In _value_i9 (Litex.Z (M := M)) := h_1163
    change (by
      let _atomic_wd_1_0 := (Litex.sub _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1162) (Litex.integerToComplex _value_i9 h_1163))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.sub _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1162) (Litex.integerToComplex _value_i9 h_1163))
      exact (Litex.subInZ _value_i8 _value_i9 h_1162 h_1163))));
  let _wd_1_4 := (Litex.number (M := M) (7 : ℂ));
  (let h_1245 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
  let h_1246 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
  let h_1247 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num));
  let h_1248 : Litex.Same _wd_1_0 _wd_1_0 := (show @Eq M.Value _ _ from Eq.refl _);
  let h_1249 : Litex.Same _wd_1_1 _wd_1_1 := (show @Eq M.Value _ _ from Eq.refl _);
  Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) => True)) h_1245 h_1246 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_1247 (fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty _wd_1_0 _wd_1_1 (2 : ℤ) (1 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_1248) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_1249) (by decide) k hlow hhigh))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
          intro _raw_i7 h_1143 _
          let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1143)
          have h_1143 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1143
          change Litex.In _value_i7 (Litex.Z (M := M))
          exact h_1143));
        let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.subValue _raw_i8 _raw_i9)) (by
          intro _raw_i8 _raw_i9 h_1162 h_1163 _
          let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1162)
          have h_1162 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1162
          let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1163)
          have h_1163 : Litex.In _value_i9 (Litex.Z (M := M)) := h_1163
          change (by
            let _atomic_wd_1_0 := (Litex.sub _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1162) (Litex.integerToComplex _value_i9 h_1163))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.sub _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1162) (Litex.integerToComplex _value_i9 h_1163))
            exact (Litex.subInZ _value_i8 _value_i9 h_1162 h_1163))));
        let _wd_1_4 := (Litex.number (M := M) (7 : ℂ));
        (let h_1245 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
        let h_1246 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
        let h_1247 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num));
        let h_1248 : Litex.Same _wd_1_0 _wd_1_0 := (show @Eq M.Value _ _ from Eq.refl _);
        let h_1249 : Litex.Same _wd_1_1 _wd_1_1 := (show @Eq M.Value _ _ from Eq.refl _);
        Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) => True)) h_1245 h_1246 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_1247 (fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty _wd_1_0 _wd_1_1 (2 : ℤ) (1 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_1248) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_1249) (by decide) k hlow hhigh))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)) from (((Eq.refl (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
          intro _raw_i7 h_1020 _
          let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1020)
          have h_1020 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1020
          change Litex.In _value_i7 (Litex.Z (M := M))
          exact h_1020));
        let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.subValue _raw_i8 _raw_i9)) (by
          intro _raw_i8 _raw_i9 h_1039 h_1040 _
          let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1039)
          have h_1039 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1039
          let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1040)
          have h_1040 : Litex.In _value_i9 (Litex.Z (M := M)) := h_1040
          change (by
            let _atomic_wd_1_0 := (Litex.sub _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1039) (Litex.integerToComplex _value_i9 h_1040))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.sub _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1039) (Litex.integerToComplex _value_i9 h_1040))
            exact (Litex.subInZ _value_i8 _value_i9 h_1039 h_1040))));
        let _wd_1_4 := (Litex.number (M := M) (7 : ℂ));
        (let h_1122 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
        let h_1123 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
        let h_1124 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num));
        let h_1125 : Litex.Same _wd_1_0 _wd_1_0 := (show @Eq M.Value _ _ from Eq.refl _);
        let h_1126 : Litex.Same _wd_1_1 _wd_1_1 := (show @Eq M.Value _ _ from Eq.refl _);
        Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) => True)) h_1122 h_1123 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_1124 (fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty _wd_1_0 _wd_1_1 (2 : ℤ) (1 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_1125) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_1126) (by decide) k hlow hhigh))))))).trans (show (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
          intro _raw_i7 h_1020 _
          let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1020)
          have h_1020 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1020
          change Litex.In _value_i7 (Litex.Z (M := M))
          exact h_1020));
        let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.subValue _raw_i8 _raw_i9)) (by
          intro _raw_i8 _raw_i9 h_1039 h_1040 _
          let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1039)
          have h_1039 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1039
          let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1040)
          have h_1040 : Litex.In _value_i9 (Litex.Z (M := M)) := h_1040
          change (by
            let _atomic_wd_1_0 := (Litex.sub _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1039) (Litex.integerToComplex _value_i9 h_1040))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.sub _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1039) (Litex.integerToComplex _value_i9 h_1040))
            exact (Litex.subInZ _value_i8 _value_i9 h_1039 h_1040))));
        let _wd_1_4 := (Litex.number (M := M) (7 : ℂ));
        (let h_1122 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
        let h_1123 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
        let h_1124 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num));
        let h_1125 : Litex.Same _wd_1_0 _wd_1_0 := (show @Eq M.Value _ _ from Eq.refl _);
        let h_1126 : Litex.Same _wd_1_1 _wd_1_1 := (show @Eq M.Value _ _ from Eq.refl _);
        Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) => True)) h_1122 h_1123 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_1124 (fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty _wd_1_0 _wd_1_1 (2 : ℤ) (1 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_1125) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_1126) (by decide) k hlow hhigh))))) = M.number (7 : ℂ) from (by
          let _fold := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
            intro _raw_i7 h_1020 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_1020)
            have h_1020 : Litex.In _value_i7 (Litex.Z (M := M)) := h_1020
            change Litex.In _value_i7 (Litex.Z (M := M))
            exact h_1020));
          let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.subValue _raw_i8 _raw_i9)) (by
            intro _raw_i8 _raw_i9 h_1039 h_1040 _
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1039)
            have h_1039 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1039
            let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1040)
            have h_1040 : Litex.In _value_i9 (Litex.Z (M := M)) := h_1040
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1039) (Litex.integerToComplex _value_i9 h_1040))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1039) (Litex.integerToComplex _value_i9 h_1040))
              exact (Litex.subInZ _value_i8 _value_i9 h_1039 h_1040))));
          let _wd_1_4 := (Litex.number (M := M) (7 : ℂ));
          (let h_1122 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
          let h_1123 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
          let h_1124 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num));
          let h_1125 : Litex.Same _wd_1_0 _wd_1_0 := (show @Eq M.Value _ _ from Eq.refl _);
          let h_1126 : Litex.Same _wd_1_1 _wd_1_1 := (show @Eq M.Value _ _ from Eq.refl _);
          Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) => True)) h_1122 h_1123 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_1124 (fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty _wd_1_0 _wd_1_1 (2 : ℤ) (1 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_1125) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_1126) (by decide) k hlow hhigh))))
          have _seed : Litex.denote _fold.val.seed = M.number (7 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (7 : ℂ)))
          apply Litex.rangeFoldDenote _fold (2 : ℤ) (1 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) (M.number (7 : ℂ))
          have _indices : Litex.integerFoldIndices (2 : ℤ) (1 : ℤ) = [] := by decide
          norm_num [Litex.foldValue, Litex.foldApply2, _indices, _seed]))).trans (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (7 : ℂ)))).symm)))
      )
  )

noncomputable def _object_w30 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => _raw_i10) (by
  intro _raw_i10 h_1266 _
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1266)
  have h_1266 : Litex.In _value_i10 (Litex.Z (M := M)) := h_1266
  change Litex.In _value_i10 (Litex.Z (M := M))
  exact h_1266));
let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.subValue _raw_i11 _raw_i12)) (by
  intro _raw_i11 _raw_i12 h_1285 h_1286 _
  let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1285)
  have h_1285 : Litex.In _value_i11 (Litex.Z (M := M)) := h_1285
  let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_1286)
  have h_1286 : Litex.In _value_i12 (Litex.Z (M := M)) := h_1286
  change (by
    let _atomic_wd_1_0 := (Litex.sub _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_1285) (Litex.integerToComplex _value_i12 h_1286))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sub _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_1285) (Litex.integerToComplex _value_i12 h_1286))
    exact (Litex.subInZ _value_i11 _value_i12 h_1285 h_1286))));
let _wd_1_4 := (Litex.number (M := M) (7 : ℂ));
(let h_1368 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
let h_1369 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
let h_1370 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num));
let h_1371 : Litex.Same _wd_1_0 _wd_1_0 := (show @Eq M.Value _ _ from Eq.refl _);
let h_1372 : Litex.Same _wd_1_1 _wd_1_1 := (show @Eq M.Value _ _ from Eq.refl _);
Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True)) h_1368 h_1369 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_1370 (fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty _wd_1_0 _wd_1_1 (2 : ℤ) (1 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_1371) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_1372) (by decide) k hlow hhigh))))

theorem h_1252 : (by
  let _equal_wd_1_0 := (_object_w30 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w30 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)) from ((show (Litex.denote _equal_wd_1_0) = M.number (7 : ℂ) from (by
          let _fold := _equal_wd_1_0
          have _seed : Litex.denote _fold.val.seed = M.number (7 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (7 : ℂ)))
          apply Litex.rangeFoldDenote _fold (2 : ℤ) (1 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) (M.number (7 : ℂ))
          have _indices : Litex.integerFoldIndices (2 : ℤ) (1 : ℤ) = [] := by decide
          norm_num [Litex.foldValue, Litex.foldApply2, _indices, _seed]))).trans (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (7 : ℂ)))).symm)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_range_x5f_folds_x2f_statement_x2e_lit
