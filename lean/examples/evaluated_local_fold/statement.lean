import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_fold_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

include M in
private theorem _sketch_1 : True := by
  have h_358 : (by
    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
    let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
    let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
      intro _raw_i1 h_372 _
      let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_372)
      have h_372 : Litex.In _value_i1 (Litex.Z (M := M)) := h_372
      change Litex.In _value_i1 (Litex.Z (M := M))
      exact h_372));
    let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_391 h_392 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_391)
      have h_391 : Litex.In _value_i2 (Litex.Z (M := M)) := h_391
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_392)
      have h_392 : Litex.In _value_i3 (Litex.Z (M := M)) := h_392
      change (by
        let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_391) (Litex.integerToComplex _value_i3 h_392))
        exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_391) (Litex.integerToComplex _value_i3 h_392))
        exact (Litex.subInZ _value_i2 _value_i3 h_391 h_392))));
    let _wd_1_4 := (Litex.number (M := M) (10 : ℂ));
    (let h_474 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
    let h_475 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
    let h_476 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num));
    Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_474 h_475 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_476 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_372 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_372)
            have h_372 : Litex.In _value_i1 (Litex.Z (M := M)) := h_372
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_372));
          let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_391 h_392 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_391)
            have h_391 : Litex.In _value_i2 (Litex.Z (M := M)) := h_391
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_392)
            have h_392 : Litex.In _value_i3 (Litex.Z (M := M)) := h_392
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_391) (Litex.integerToComplex _value_i3 h_392))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_391) (Litex.integerToComplex _value_i3 h_392))
              exact (Litex.subInZ _value_i2 _value_i3 h_391 h_392))));
          let _wd_1_4 := (Litex.number (M := M) (10 : ℂ));
          (let h_474 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
          let h_475 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
          let h_476 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num));
          Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_474 h_475 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_476 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)));
          (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) (((Eq.refl (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_15 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_15)
            have h_15 : Litex.In _value_i1 (Litex.Z (M := M)) := h_15
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_15));
          let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_34 h_35 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_34)
            have h_34 : Litex.In _value_i2 (Litex.Z (M := M)) := h_34
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_35)
            have h_35 : Litex.In _value_i3 (Litex.Z (M := M)) := h_35
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_34) (Litex.integerToComplex _value_i3 h_35))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_34) (Litex.integerToComplex _value_i3 h_35))
              exact (Litex.subInZ _value_i2 _value_i3 h_34 h_35))));
          let _wd_1_4 := (Litex.number (M := M) (10 : ℂ));
          (let h_117 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
          let h_118 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
          let h_119 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num));
          Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_117 h_118 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_119 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))))).trans (show (Litex.denote (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_15 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_15)
            have h_15 : Litex.In _value_i1 (Litex.Z (M := M)) := h_15
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_15));
          let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_34 h_35 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_34)
            have h_34 : Litex.In _value_i2 (Litex.Z (M := M)) := h_34
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_35)
            have h_35 : Litex.In _value_i3 (Litex.Z (M := M)) := h_35
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_34) (Litex.integerToComplex _value_i3 h_35))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_34) (Litex.integerToComplex _value_i3 h_35))
              exact (Litex.subInZ _value_i2 _value_i3 h_34 h_35))));
          let _wd_1_4 := (Litex.number (M := M) (10 : ℂ));
          (let h_117 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
          let h_118 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
          let h_119 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num));
          Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_117 h_118 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_119 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))) = M.number (5 : ℂ) from (by
            let _fold := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
            let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
            let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
              intro _raw_i1 h_15 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_15)
              have h_15 : Litex.In _value_i1 (Litex.Z (M := M)) := h_15
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_15));
            let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_34 h_35 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_34)
              have h_34 : Litex.In _value_i2 (Litex.Z (M := M)) := h_34
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_35)
              have h_35 : Litex.In _value_i3 (Litex.Z (M := M)) := h_35
              change (by
                let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_34) (Litex.integerToComplex _value_i3 h_35))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_34) (Litex.integerToComplex _value_i3 h_35))
                exact (Litex.subInZ _value_i2 _value_i3 h_34 h_35))));
            let _wd_1_4 := (Litex.number (M := M) (10 : ℂ));
            (let h_117 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
            let h_118 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
            let h_119 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num));
            Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_117 h_118 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_119 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))
            have _seed : Litex.denote _fold.val.seed = M.number (10 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (10 : ℂ))).trans (congrArg M.number (by norm_num : (10 : ℂ) = (10 : ℂ)))
            have _term_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (2 : ℂ)) = M.number (2 : ℂ) := (by
              let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
              intro _raw_i1 h_135 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_135)
              have h_135 : Litex.In _value_i1 (Litex.Z (M := M)) := h_135
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_135));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
              let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
              intro _raw_i1 h_135 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_135)
              have h_135 : Litex.In _value_i1 (Litex.Z (M := M)) := h_135
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_135))
              have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
              have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
              have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
              have _argument_0 : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
              have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := by change (fun (_raw_i1 : M.Value) => _raw_i1) (Litex.denote _call.val.argument) = (M.number (2 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
            have _step_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (10 : ℂ)) (M.number (2 : ℂ))) = M.number (8 : ℂ) := (by
              let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_155 h_156 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_155)
              have h_155 : Litex.In _value_i2 (Litex.Z (M := M)) := h_155
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_156)
              have h_156 : Litex.In _value_i3 (Litex.Z (M := M)) := h_156
              change (by
                let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_155) (Litex.integerToComplex _value_i3 h_156))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_155) (Litex.integerToComplex _value_i3 h_156))
                exact (Litex.subInZ _value_i2 _value_i3 h_155 h_156))));
            let _wd_1_1 := (Litex.number (M := M) (10 : ℂ));
            let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
              let _literal := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_155 h_156 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_155)
              have h_155 : Litex.In _value_i2 (Litex.Z (M := M)) := h_155
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_156)
              have h_156 : Litex.In _value_i3 (Litex.Z (M := M)) := h_156
              change (by
                let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_155) (Litex.integerToComplex _value_i3 h_156))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_155) (Litex.integerToComplex _value_i3 h_156))
                exact (Litex.subInZ _value_i2 _value_i3 h_155 h_156))))
              have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
              have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
              have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _ _).mpr _call.wd.2)
              have _argument_0 : Litex.denote _call.val.first = M.number (10 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (10 : ℂ))).trans (congrArg M.number (by norm_num : (10 : ℂ) = (10 : ℂ)))
              have _argument_1 : Litex.denote _call.val.second = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
              have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (10 : ℂ)) (M.number (2 : ℂ))) := by change (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (10 : ℂ)) (M.number (2 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              have _calculated : (M.subValue (M.number (10 : ℂ)) (M.number (2 : ℂ))) = M.number (8 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
            have _term_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (3 : ℂ)) = M.number (3 : ℂ) := (by
              let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
              intro _raw_i1 h_253 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_253)
              have h_253 : Litex.In _value_i1 (Litex.Z (M := M)) := h_253
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_253));
            let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
            (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
              let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
              intro _raw_i1 h_253 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_253)
              have h_253 : Litex.In _value_i1 (Litex.Z (M := M)) := h_253
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_253))
              have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
              have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
              have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
              have _argument_0 : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
              have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := by change (fun (_raw_i1 : M.Value) => _raw_i1) (Litex.denote _call.val.argument) = (M.number (3 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
            have _step_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (8 : ℂ)) (M.number (3 : ℂ))) = M.number (5 : ℂ) := (by
              let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_273 h_274 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_273)
              have h_273 : Litex.In _value_i2 (Litex.Z (M := M)) := h_273
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_274)
              have h_274 : Litex.In _value_i3 (Litex.Z (M := M)) := h_274
              change (by
                let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_273) (Litex.integerToComplex _value_i3 h_274))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_273) (Litex.integerToComplex _value_i3 h_274))
                exact (Litex.subInZ _value_i2 _value_i3 h_273 h_274))));
            let _wd_1_1 := (Litex.number (M := M) (8 : ℂ));
            let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (8 : ℂ) (8 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
              let _literal := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_273 h_274 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_273)
              have h_273 : Litex.In _value_i2 (Litex.Z (M := M)) := h_273
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_274)
              have h_274 : Litex.In _value_i3 (Litex.Z (M := M)) := h_274
              change (by
                let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_273) (Litex.integerToComplex _value_i3 h_274))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_273) (Litex.integerToComplex _value_i3 h_274))
                exact (Litex.subInZ _value_i2 _value_i3 h_273 h_274))))
              have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
              have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
              have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _ _).mpr _call.wd.2)
              have _argument_0 : Litex.denote _call.val.first = M.number (8 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ))).trans (congrArg M.number (by norm_num : (8 : ℂ) = (8 : ℂ)))
              have _argument_1 : Litex.denote _call.val.second = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
              have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (8 : ℂ)) (M.number (3 : ℂ))) := by change (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (8 : ℂ)) (M.number (3 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              have _calculated : (M.subValue (M.number (8 : ℂ)) (M.number (3 : ℂ))) = M.number (5 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
            apply Litex.rangeFoldDenote _fold (2 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (M.number (5 : ℂ))
            have _indices : Litex.integerFoldIndices (2 : ℤ) (3 : ℤ) = [(2 : ℤ), (3 : ℤ)] := by decide
            norm_num [Litex.foldValue, Litex.foldApply2, _indices, _seed, _term_0, _step_0, _term_1, _step_1]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (5 : ℂ)))).symm)))
        )
    )
  let _object_w17 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
  let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
    intro _raw_i4 h_492 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_492)
    have h_492 : Litex.In _value_i4 (Litex.Z (M := M)) := h_492
    change Litex.In _value_i4 (Litex.Z (M := M))
    exact h_492));
  let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.subValue _raw_i5 _raw_i6)) (by
    intro _raw_i5 _raw_i6 h_511 h_512 _
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_511)
    have h_511 : Litex.In _value_i5 (Litex.Z (M := M)) := h_511
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_512)
    have h_512 : Litex.In _value_i6 (Litex.Z (M := M)) := h_512
    change (by
      let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_511) (Litex.integerToComplex _value_i6 h_512))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_511) (Litex.integerToComplex _value_i6 h_512))
      exact (Litex.subInZ _value_i5 _value_i6 h_511 h_512))));
  let _wd_1_4 := (Litex.number (M := M) (10 : ℂ));
  (let h_594 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
  let h_595 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
  let h_596 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num));
  Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True)) h_594 h_595 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_596 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i4 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))

  have h_1 : (by
    let _equal_wd_1_0 := _object_w17
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (let _equal_wd_1_0 := _object_w17;
          (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) ((show (Litex.denote _equal_wd_1_0) = M.number (5 : ℂ) from (by
            let _fold := _equal_wd_1_0
            have _seed : Litex.denote _fold.val.seed = M.number (10 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (10 : ℂ))).trans (congrArg M.number (by norm_num : (10 : ℂ) = (10 : ℂ)))
            have _term_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (2 : ℂ)) = M.number (2 : ℂ) := (by
              let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
              intro _raw_i4 h_603 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_603)
              have h_603 : Litex.In _value_i4 (Litex.Z (M := M)) := h_603
              change Litex.In _value_i4 (Litex.Z (M := M))
              exact h_603));
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
            have _step_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (10 : ℂ)) (M.number (2 : ℂ))) = M.number (8 : ℂ) := (by
              let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.subValue _raw_i5 _raw_i6)) (by
              intro _raw_i5 _raw_i6 h_612 h_613 _
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_612)
              have h_612 : Litex.In _value_i5 (Litex.Z (M := M)) := h_612
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_613)
              have h_613 : Litex.In _value_i6 (Litex.Z (M := M)) := h_613
              change (by
                let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_612) (Litex.integerToComplex _value_i6 h_613))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_612) (Litex.integerToComplex _value_i6 h_613))
                exact (Litex.subInZ _value_i5 _value_i6 h_612 h_613))));
            let _wd_1_1 := (Litex.number (M := M) (10 : ℂ));
            let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (10 : ℂ) (10 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
              let _literal := (_equal_wd_1_0).val.operation
              have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
              have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
              have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _ _).mpr _call.wd.2)
              have _argument_0 : Litex.denote _call.val.first = M.number (10 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (10 : ℂ))).trans (congrArg M.number (by norm_num : (10 : ℂ) = (10 : ℂ)))
              have _argument_1 : Litex.denote _call.val.second = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
              have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (10 : ℂ)) (M.number (2 : ℂ))) := by change (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.subValue _raw_i5 _raw_i6)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (10 : ℂ)) (M.number (2 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              have _calculated : (M.subValue (M.number (10 : ℂ)) (M.number (2 : ℂ))) = M.number (8 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
            have _term_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (3 : ℂ)) = M.number (3 : ℂ) := (by
              let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
              intro _raw_i4 h_699 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_699)
              have h_699 : Litex.In _value_i4 (Litex.Z (M := M)) := h_699
              change Litex.In _value_i4 (Litex.Z (M := M))
              exact h_699));
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
            have _step_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (8 : ℂ)) (M.number (3 : ℂ))) = M.number (5 : ℂ) := (by
              let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.subValue _raw_i5 _raw_i6)) (by
              intro _raw_i5 _raw_i6 h_708 h_709 _
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_708)
              have h_708 : Litex.In _value_i5 (Litex.Z (M := M)) := h_708
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_709)
              have h_709 : Litex.In _value_i6 (Litex.Z (M := M)) := h_709
              change (by
                let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_708) (Litex.integerToComplex _value_i6 h_709))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_708) (Litex.integerToComplex _value_i6 h_709))
                exact (Litex.subInZ _value_i5 _value_i6 h_708 h_709))));
            let _wd_1_1 := (Litex.number (M := M) (8 : ℂ));
            let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (8 : ℂ) (8 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
              let _literal := (_equal_wd_1_0).val.operation
              have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
              have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
              have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _ _).mpr _call.wd.2)
              have _argument_0 : Litex.denote _call.val.first = M.number (8 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ))).trans (congrArg M.number (by norm_num : (8 : ℂ) = (8 : ℂ)))
              have _argument_1 : Litex.denote _call.val.second = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
              have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (8 : ℂ)) (M.number (3 : ℂ))) := by change (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.subValue _raw_i5 _raw_i6)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (8 : ℂ)) (M.number (3 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              have _calculated : (M.subValue (M.number (8 : ℂ)) (M.number (3 : ℂ))) = M.number (5 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
              exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
            apply Litex.rangeFoldDenote _fold (2 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (M.number (5 : ℂ))
            have _indices : Litex.integerFoldIndices (2 : ℤ) (3 : ℤ) = [(2 : ℤ), (3 : ℤ)] := by decide
            norm_num [Litex.foldValue, Litex.foldApply2, _indices, _seed, _term_0, _step_0, _term_1, _step_1]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (5 : ℂ)))).symm)))
        )
    )
  exact True.intro
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_fold_x2f_statement_x2e_lit
