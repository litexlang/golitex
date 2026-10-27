import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_fold_x5f_bound_x5f_names_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_w5 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
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
let _wd_1_4 := (Litex.number (M := M) (0 : ℂ));
(let h_117 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
let h_118 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
let h_119 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_117 h_118 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_119 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))

noncomputable def _object_w6 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
  intro _raw_i4 h_135 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_135)
  have h_135 : Litex.In _value_i4 (Litex.Z (M := M)) := h_135
  change Litex.In _value_i4 (Litex.Z (M := M))
  exact h_135));
let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (M.subValue _raw_i5 _raw_i6)) (by
  intro _raw_i5 _raw_i6 h_154 h_155 _
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_154)
  have h_154 : Litex.In _value_i5 (Litex.Z (M := M)) := h_154
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_155)
  have h_155 : Litex.In _value_i6 (Litex.Z (M := M)) := h_155
  change (by
    let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_154) (Litex.integerToComplex _value_i6 h_155))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sub _value_i5 _value_i6 (Litex.integerToComplex _value_i5 h_154) (Litex.integerToComplex _value_i6 h_155))
    exact (Litex.subInZ _value_i5 _value_i6 h_154 h_155))));
let _wd_1_4 := (Litex.number (M := M) (0 : ℂ));
(let h_237 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
let h_238 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num));
let h_239 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True)) h_237 h_238 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_239 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i4 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  let _equal_wd_1_1 := (_object_w6 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        let _equal_wd_1_1 := (_object_w6 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
          let _left := _equal_wd_1_0
          let _right := _equal_wd_1_1
          exact (show Litex.Same _left _right from rfl))))
      )
  )

noncomputable def _object_w43 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
  intro _raw_i7 h_258 _
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_258)
  have h_258 : Litex.In _value_i7 (Litex.Z (M := M)) := h_258
  change Litex.In _value_i7 (Litex.Z (M := M))
  exact h_258));
let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
  intro _raw_i8 _raw_i9 h_277 h_278 _
  let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_277)
  have h_277 : Litex.In _value_i8 (Litex.Z (M := M)) := h_277
  let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_278)
  have h_278 : Litex.In _value_i9 (Litex.Z (M := M)) := h_278
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_277) (Litex.integerToComplex _value_i9 h_278))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_277) (Litex.integerToComplex _value_i9 h_278))
    exact (Litex.addInZ _value_i8 _value_i9 h_277 h_278))));
let _wd_1_3 := (Litex.number (M := M) (0 : ℂ));
(let h_360 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0));
let h_362 : Litex.In _wd_1_3 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
let h_367 : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_380 : Litex.In _value_i13 (Litex.Z (M := M))) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_381 : Litex.In _value_i14 (Litex.Z (M := M))), (by
  let _object_w10 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_395 h_396 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_395)
    have h_395 : Litex.In _value_i8 (Litex.Z (M := M)) := h_395
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_396)
    have h_396 : Litex.In _value_i9 (Litex.Z (M := M)) := h_396
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_395) (Litex.integerToComplex _value_i9 h_396))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_395) (Litex.integerToComplex _value_i9 h_396))
      exact (Litex.addInZ _value_i8 _value_i9 h_395 h_396))));
  let _wd_2_1 := _value_i13;
  let _wd_2_2 := _value_i14;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_380 h_381 True.intro))
  let _object_w11 := (Litex.add _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_380) (Litex.integerToComplex _value_i14 h_381))
  let _object_w12 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_1495 h_1496 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1495)
    have h_1495 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1495
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1496)
    have h_1496 : Litex.In _value_i9 (Litex.Z (M := M)) := h_1496
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1495) (Litex.integerToComplex _value_i9 h_1496))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1495) (Litex.integerToComplex _value_i9 h_1496))
      exact (Litex.addInZ _value_i8 _value_i9 h_1495 h_1496))));
  let _wd_2_1 := _value_i14;
  let _wd_2_2 := _value_i13;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_381 h_380 True.intro))
  let _object_w13 := (Litex.add _value_i14 _value_i13 (Litex.integerToComplex _value_i14 h_381) (Litex.integerToComplex _value_i13 h_380))
  exact (((by
    let _equal_wd_1_0 := _object_w10
    let _equal_wd_1_1 := _object_w11
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w12
    let _equal_wd_1_1 := _object_w13
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w11
    let _equal_wd_1_1 := _object_w13
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w10
    let _equal_wd_1_1 := _object_w12
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
) := (by
  intro _Host_i13 _rep_i13 _value_i13 h_380 _Host_i14 _rep_i14 _value_i14 h_381
  let _object_w10 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_395 h_396 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_395)
    have h_395 : Litex.In _value_i8 (Litex.Z (M := M)) := h_395
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_396)
    have h_396 : Litex.In _value_i9 (Litex.Z (M := M)) := h_396
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_395) (Litex.integerToComplex _value_i9 h_396))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_395) (Litex.integerToComplex _value_i9 h_396))
      exact (Litex.addInZ _value_i8 _value_i9 h_395 h_396))));
  let _wd_2_1 := _value_i13;
  let _wd_2_2 := _value_i14;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_380 h_381 True.intro))
  let _object_w11 := (Litex.add _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_380) (Litex.integerToComplex _value_i14 h_381))
  have h_363 : (by
    let _equal_wd_1_0 := _object_w10
    let _equal_wd_1_1 := _object_w11
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
              intro _raw_i8 _raw_i9 h_1134 h_1135 _
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1134)
              have h_1134 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1134
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1135)
              have h_1135 : Litex.In _value_i9 (Litex.Z (M := M)) := h_1135
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1134) (Litex.integerToComplex _value_i9 h_1135))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1134) (Litex.integerToComplex _value_i9 h_1135))
                exact (Litex.addInZ _value_i8 _value_i9 h_1134 h_1135))));
            let _wd_2_1 := _value_i13;
            let _wd_2_2 := _value_i14;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_380 h_381 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
              intro _raw_i8 _raw_i9 h_1281 h_1282 _
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1281)
              have h_1281 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1281
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1282)
              have h_1282 : Litex.In _value_i9 (Litex.Z (M := M)) := h_1282
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1281) (Litex.integerToComplex _value_i9 h_1282))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1281) (Litex.integerToComplex _value_i9 h_1282))
                exact (Litex.addInZ _value_i8 _value_i9 h_1281 h_1282))));
            let _wd_2_1 := _value_i13;
            let _wd_2_2 := _value_i14;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_380 h_381 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w12 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_1495 h_1496 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1495)
    have h_1495 : Litex.In _value_i8 (Litex.Z (M := M)) := h_1495
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1496)
    have h_1496 : Litex.In _value_i9 (Litex.Z (M := M)) := h_1496
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1495) (Litex.integerToComplex _value_i9 h_1496))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_1495) (Litex.integerToComplex _value_i9 h_1496))
      exact (Litex.addInZ _value_i8 _value_i9 h_1495 h_1496))));
  let _wd_2_1 := _value_i14;
  let _wd_2_2 := _value_i13;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_381 h_380 True.intro))
  let _object_w13 := (Litex.add _value_i14 _value_i13 (Litex.integerToComplex _value_i14 h_381) (Litex.integerToComplex _value_i13 h_380))
  have h_364 : (by
    let _equal_wd_1_0 := _object_w12
    let _equal_wd_1_1 := _object_w13
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i14), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i13)) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i13)) = (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i13)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i14), (Litex.denote _value_i13)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i14), (Litex.denote _value_i13)])) = (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i13)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
              intro _raw_i8 _raw_i9 h_2234 h_2235 _
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_2234)
              have h_2234 : Litex.In _value_i8 (Litex.Z (M := M)) := h_2234
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_2235)
              have h_2235 : Litex.In _value_i9 (Litex.Z (M := M)) := h_2235
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_2234) (Litex.integerToComplex _value_i9 h_2235))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_2234) (Litex.integerToComplex _value_i9 h_2235))
                exact (Litex.addInZ _value_i8 _value_i9 h_2234 h_2235))));
            let _wd_2_1 := _value_i14;
            let _wd_2_2 := _value_i13;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_381 h_380 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
              intro _raw_i8 _raw_i9 h_2381 h_2382 _
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_2381)
              have h_2381 : Litex.In _value_i8 (Litex.Z (M := M)) := h_2381
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_2382)
              have h_2382 : Litex.In _value_i9 (Litex.Z (M := M)) := h_2382
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_2381) (Litex.integerToComplex _value_i9 h_2382))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_2381) (Litex.integerToComplex _value_i9 h_2382))
                exact (Litex.addInZ _value_i8 _value_i9 h_2381 h_2382))));
            let _wd_2_1 := _value_i14;
            let _wd_2_2 := _value_i13;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_381 h_380 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i13)) from rfl))
          ))).trans _litex_residual)
        )
    )
  have h_365 : (by
    let _equal_wd_1_0 := _object_w11
    let _equal_wd_1_1 := _object_w13
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_380)) + (Litex.NativeBridge.asComplex _value_i14 (Litex.integerToComplex _value_i14 h_381))) ((Litex.NativeBridge.asComplex _value_i14 (Litex.integerToComplex _value_i14 h_381)) + (Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_380))) (Litex.NativeBridge.denoteAdd _value_i13 _value_i14 (_object_w11).wd.1 (_object_w11).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_380)) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.integerToComplex _value_i14 h_381))) (Litex.NativeBridge.denoteAdd _value_i14 _value_i13 (_object_w13).wd.1 (_object_w13).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.integerToComplex _value_i14 h_381)) (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_380))) (by ring!))
        )
    )
  have h_366 : (by
    let _equal_wd_1_0 := _object_w10
    let _equal_wd_1_1 := _object_w12
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          ((((h_363).trans h_365)).trans (h_364).symm)
        )
    )
  exact (And.intro h_363 (And.intro h_364 (And.intro h_365 h_366)))
);
let h_2595 : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_2608 : Litex.In _value_i13 (Litex.Z (M := M))) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_2609 : Litex.In _value_i14 (Litex.Z (M := M))) {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_2610 : Litex.In _value_i15 (Litex.Z (M := M))), (by
  let _object_w15 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_2624 h_2625 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_2624)
    have h_2624 : Litex.In _value_i8 (Litex.Z (M := M)) := h_2624
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_2625)
    have h_2625 : Litex.In _value_i9 (Litex.Z (M := M)) := h_2625
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_2624) (Litex.integerToComplex _value_i9 h_2625))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_2624) (Litex.integerToComplex _value_i9 h_2625))
      exact (Litex.addInZ _value_i8 _value_i9 h_2624 h_2625))));
  let _wd_2_1 := _value_i13;
  let _wd_2_2 := _value_i14;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2608 h_2609 True.intro))
  let _object_w16 := (Litex.add _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_2608) (Litex.integerToComplex _value_i14 h_2609))
  let _object_w17 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_3888 h_3889 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_3888)
    have h_3888 : Litex.In _value_i8 (Litex.Z (M := M)) := h_3888
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_3889)
    have h_3889 : Litex.In _value_i9 (Litex.Z (M := M)) := h_3889
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_3888) (Litex.integerToComplex _value_i9 h_3889))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_3888) (Litex.integerToComplex _value_i9 h_3889))
      exact (Litex.addInZ _value_i8 _value_i9 h_3888 h_3889))));
  let _wd_2_1 := _value_i14;
  let _wd_2_2 := _value_i15;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2609 h_2610 True.intro))
  let _object_w18 := (Litex.add _value_i14 _value_i15 (Litex.integerToComplex _value_i14 h_2609) (Litex.integerToComplex _value_i15 h_2610))
  let _object_w19 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_5180 h_5181 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_5180)
    have h_5180 : Litex.In _value_i8 (Litex.Z (M := M)) := h_5180
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_5181)
    have h_5181 : Litex.In _value_i9 (Litex.Z (M := M)) := h_5181
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_5180) (Litex.integerToComplex _value_i9 h_5181))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_5180) (Litex.integerToComplex _value_i9 h_5181))
      exact (Litex.addInZ _value_i8 _value_i9 h_5180 h_5181))));
  let _wd_2_1 := _object_w15;
  let _wd_2_2 := _value_i15;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w15
    exact (Litex.inOfSame _object_w15 _object_w15 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w15) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w15))) h_2610 True.intro))
  let _object_w20 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_5382 h_5383 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_5382)
    have h_5382 : Litex.In _value_i8 (Litex.Z (M := M)) := h_5382
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_5383)
    have h_5383 : Litex.In _value_i9 (Litex.Z (M := M)) := h_5383
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_5382) (Litex.integerToComplex _value_i9 h_5383))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_5382) (Litex.integerToComplex _value_i9 h_5383))
      exact (Litex.addInZ _value_i8 _value_i9 h_5382 h_5383))));
  let _wd_2_1 := _object_w16;
  let _wd_2_2 := _value_i15;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w16
    exact (Litex.addInZ _value_i13 _value_i14 h_2608 h_2609)) h_2610 True.intro))
  let _object_w21 := (let _wd_2_0 := _object_w16;
  let _wd_2_1 := _value_i15;
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _object_w16
    exact (Litex.addInC _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_2608) (Litex.integerToComplex _value_i14 h_2609))) (Litex.integerToComplex _wd_2_1 h_2610)))
  let _object_w22 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_6116 h_6117 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_6116)
    have h_6116 : Litex.In _value_i8 (Litex.Z (M := M)) := h_6116
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_6117)
    have h_6117 : Litex.In _value_i9 (Litex.Z (M := M)) := h_6117
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_6116) (Litex.integerToComplex _value_i9 h_6117))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_6116) (Litex.integerToComplex _value_i9 h_6117))
      exact (Litex.addInZ _value_i8 _value_i9 h_6116 h_6117))));
  let _wd_2_1 := _value_i13;
  let _wd_2_2 := _object_w17;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2608 (by
    let _atomic_wd_1_0 := _object_w17
    exact (Litex.inOfSame _object_w17 _object_w17 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w17) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w17))) True.intro))
  let _object_w23 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_6314 h_6315 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_6314)
    have h_6314 : Litex.In _value_i8 (Litex.Z (M := M)) := h_6314
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_6315)
    have h_6315 : Litex.In _value_i9 (Litex.Z (M := M)) := h_6315
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_6314) (Litex.integerToComplex _value_i9 h_6315))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_6314) (Litex.integerToComplex _value_i9 h_6315))
      exact (Litex.addInZ _value_i8 _value_i9 h_6314 h_6315))));
  let _wd_2_1 := _value_i13;
  let _wd_2_2 := _object_w18;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2608 (by
    let _atomic_wd_1_0 := _object_w18
    exact (Litex.addInZ _value_i14 _value_i15 h_2609 h_2610)) True.intro))
  let _object_w24 := (let _wd_2_0 := _value_i13;
  let _wd_2_1 := _object_w18;
  (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_2608) (by
    let _atomic_wd_1_0 := _object_w18
    exact (Litex.addInC _value_i14 _value_i15 (Litex.integerToComplex _value_i14 h_2609) (Litex.integerToComplex _value_i15 h_2610)))))
  exact (((by
    let _equal_wd_1_0 := _object_w15
    let _equal_wd_1_1 := _object_w16
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w17
    let _equal_wd_1_1 := _object_w18
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w19
    let _equal_wd_1_1 := _object_w20
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w20
    let _equal_wd_1_1 := _object_w21
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w22
    let _equal_wd_1_1 := _object_w23
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w23
    let _equal_wd_1_1 := _object_w24
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w21
    let _equal_wd_1_1 := _object_w24
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w19
    let _equal_wd_1_1 := _object_w22
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
) := (by
  intro _Host_i13 _rep_i13 _value_i13 h_2608 _Host_i14 _rep_i14 _value_i14 h_2609 _Host_i15 _rep_i15 _value_i15 h_2610
  let _object_w15 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_2624 h_2625 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_2624)
    have h_2624 : Litex.In _value_i8 (Litex.Z (M := M)) := h_2624
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_2625)
    have h_2625 : Litex.In _value_i9 (Litex.Z (M := M)) := h_2625
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_2624) (Litex.integerToComplex _value_i9 h_2625))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_2624) (Litex.integerToComplex _value_i9 h_2625))
      exact (Litex.addInZ _value_i8 _value_i9 h_2624 h_2625))));
  let _wd_2_1 := _value_i13;
  let _wd_2_2 := _value_i14;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2608 h_2609 True.intro))
  let _object_w16 := (Litex.add _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_2608) (Litex.integerToComplex _value_i14 h_2609))
  have h_2587 : (by
    let _equal_wd_1_0 := _object_w15
    let _equal_wd_1_1 := _object_w16
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (Litex.denote _value_i14)])) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
              intro _raw_i8 _raw_i9 h_3471 h_3472 _
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_3471)
              have h_3471 : Litex.In _value_i8 (Litex.Z (M := M)) := h_3471
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_3472)
              have h_3472 : Litex.In _value_i9 (Litex.Z (M := M)) := h_3472
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_3471) (Litex.integerToComplex _value_i9 h_3472))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_3471) (Litex.integerToComplex _value_i9 h_3472))
                exact (Litex.addInZ _value_i8 _value_i9 h_3471 h_3472))));
            let _wd_2_1 := _value_i13;
            let _wd_2_2 := _value_i14;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2608 h_2609 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
              intro _raw_i8 _raw_i9 h_3638 h_3639 _
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_3638)
              have h_3638 : Litex.In _value_i8 (Litex.Z (M := M)) := h_3638
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_3639)
              have h_3639 : Litex.In _value_i9 (Litex.Z (M := M)) := h_3639
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_3638) (Litex.integerToComplex _value_i9 h_3639))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_3638) (Litex.integerToComplex _value_i9 h_3639))
                exact (Litex.addInZ _value_i8 _value_i9 h_3638 h_3639))));
            let _wd_2_1 := _value_i13;
            let _wd_2_2 := _value_i14;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2608 h_2609 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w17 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_3888 h_3889 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_3888)
    have h_3888 : Litex.In _value_i8 (Litex.Z (M := M)) := h_3888
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_3889)
    have h_3889 : Litex.In _value_i9 (Litex.Z (M := M)) := h_3889
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_3888) (Litex.integerToComplex _value_i9 h_3889))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_3888) (Litex.integerToComplex _value_i9 h_3889))
      exact (Litex.addInZ _value_i8 _value_i9 h_3888 h_3889))));
  let _wd_2_1 := _value_i14;
  let _wd_2_2 := _value_i15;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2609 h_2610 True.intro))
  let _object_w18 := (Litex.add _value_i14 _value_i15 (Litex.integerToComplex _value_i14 h_2609) (Litex.integerToComplex _value_i15 h_2610))
  have h_2588 : (by
    let _equal_wd_1_0 := _object_w17
    let _equal_wd_1_1 := _object_w18
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i14), (Litex.denote _value_i15)])) = (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i15)) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i15)) = (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i15)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i14), (Litex.denote _value_i15)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i14), (Litex.denote _value_i15)])) = (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i15)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
              intro _raw_i8 _raw_i9 h_4755 h_4756 _
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4755)
              have h_4755 : Litex.In _value_i8 (Litex.Z (M := M)) := h_4755
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_4756)
              have h_4756 : Litex.In _value_i9 (Litex.Z (M := M)) := h_4756
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_4755) (Litex.integerToComplex _value_i9 h_4756))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_4755) (Litex.integerToComplex _value_i9 h_4756))
                exact (Litex.addInZ _value_i8 _value_i9 h_4755 h_4756))));
            let _wd_2_1 := _value_i14;
            let _wd_2_2 := _value_i15;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2609 h_2610 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
              intro _raw_i8 _raw_i9 h_4926 h_4927 _
              let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_4926)
              have h_4926 : Litex.In _value_i8 (Litex.Z (M := M)) := h_4926
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_4927)
              have h_4927 : Litex.In _value_i9 (Litex.Z (M := M)) := h_4927
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_4926) (Litex.integerToComplex _value_i9 h_4927))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_4926) (Litex.integerToComplex _value_i9 h_4927))
                exact (Litex.addInZ _value_i8 _value_i9 h_4926 h_4927))));
            let _wd_2_1 := _value_i14;
            let _wd_2_2 := _value_i15;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2609 h_2610 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i15)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w19 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_5180 h_5181 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_5180)
    have h_5180 : Litex.In _value_i8 (Litex.Z (M := M)) := h_5180
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_5181)
    have h_5181 : Litex.In _value_i9 (Litex.Z (M := M)) := h_5181
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_5180) (Litex.integerToComplex _value_i9 h_5181))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_5180) (Litex.integerToComplex _value_i9 h_5181))
      exact (Litex.addInZ _value_i8 _value_i9 h_5180 h_5181))));
  let _wd_2_1 := _object_w15;
  let _wd_2_2 := _value_i15;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w15
    exact (Litex.inOfSame _object_w15 _object_w15 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w15) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w15))) h_2610 True.intro))
  let _object_w20 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_5382 h_5383 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_5382)
    have h_5382 : Litex.In _value_i8 (Litex.Z (M := M)) := h_5382
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_5383)
    have h_5383 : Litex.In _value_i9 (Litex.Z (M := M)) := h_5383
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_5382) (Litex.integerToComplex _value_i9 h_5383))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_5382) (Litex.integerToComplex _value_i9 h_5383))
      exact (Litex.addInZ _value_i8 _value_i9 h_5382 h_5383))));
  let _wd_2_1 := _object_w16;
  let _wd_2_2 := _value_i15;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w16
    exact (Litex.addInZ _value_i13 _value_i14 h_2608 h_2609)) h_2610 True.intro))
  have h_2589 : (by
    let _equal_wd_1_0 := _object_w19
    let _equal_wd_1_1 := _object_w20
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_2587 (show @Eq M.Value _ _ from Eq.refl _)))
        )
    )
  let _object_w21 := (let _wd_2_0 := _object_w16;
  let _wd_2_1 := _value_i15;
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _object_w16
    exact (Litex.addInC _value_i13 _value_i14 (Litex.integerToComplex _value_i13 h_2608) (Litex.integerToComplex _value_i14 h_2609))) (Litex.integerToComplex _wd_2_1 h_2610)))
  have h_2590 : (by
    let _equal_wd_1_0 := _object_w20
    let _equal_wd_1_1 := _object_w21
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)), (Litex.denote _value_i15)])) = (M.addValue (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) (Litex.denote _value_i15)) from by
            have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) (Litex.denote _value_i15)) = (M.addValue (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) (Litex.denote _value_i15)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)), (Litex.denote _value_i15)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)), (Litex.denote _value_i15)])) = (M.addValue (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) (Litex.denote _value_i15)) from by
            let _litex_original := _object_w20
            let _litex_literal := _object_w20
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i13) (Litex.denote _value_i14)) (Litex.denote _value_i15)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w22 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_6116 h_6117 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_6116)
    have h_6116 : Litex.In _value_i8 (Litex.Z (M := M)) := h_6116
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_6117)
    have h_6117 : Litex.In _value_i9 (Litex.Z (M := M)) := h_6117
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_6116) (Litex.integerToComplex _value_i9 h_6117))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_6116) (Litex.integerToComplex _value_i9 h_6117))
      exact (Litex.addInZ _value_i8 _value_i9 h_6116 h_6117))));
  let _wd_2_1 := _value_i13;
  let _wd_2_2 := _object_w17;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2608 (by
    let _atomic_wd_1_0 := _object_w17
    exact (Litex.inOfSame _object_w17 _object_w17 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w17) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w17))) True.intro))
  let _object_w23 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by
    intro _raw_i8 _raw_i9 h_6314 h_6315 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_6314)
    have h_6314 : Litex.In _value_i8 (Litex.Z (M := M)) := h_6314
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_6315)
    have h_6315 : Litex.In _value_i9 (Litex.Z (M := M)) := h_6315
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_6314) (Litex.integerToComplex _value_i9 h_6315))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 _value_i9 (Litex.integerToComplex _value_i8 h_6314) (Litex.integerToComplex _value_i9 h_6315))
      exact (Litex.addInZ _value_i8 _value_i9 h_6314 h_6315))));
  let _wd_2_1 := _value_i13;
  let _wd_2_2 := _object_w18;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_2608 (by
    let _atomic_wd_1_0 := _object_w18
    exact (Litex.addInZ _value_i14 _value_i15 h_2609 h_2610)) True.intro))
  have h_2591 : (by
    let _equal_wd_1_0 := _object_w22
    let _equal_wd_1_1 := _object_w23
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_2588))
        )
    )
  let _object_w24 := (let _wd_2_0 := _value_i13;
  let _wd_2_1 := _object_w18;
  (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_2608) (by
    let _atomic_wd_1_0 := _object_w18
    exact (Litex.addInC _value_i14 _value_i15 (Litex.integerToComplex _value_i14 h_2609) (Litex.integerToComplex _value_i15 h_2610)))))
  have h_2592 : (by
    let _equal_wd_1_0 := _object_w23
    let _equal_wd_1_1 := _object_w24
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i15))])) = (M.addValue (Litex.denote _value_i13) (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i15))) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i13) (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i15))) = (M.addValue (Litex.denote _value_i13) (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i15))) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i15))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i13), (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i15))])) = (M.addValue (Litex.denote _value_i13) (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i15))) from by
            let _litex_original := _object_w23
            let _litex_literal := _object_w23
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => (M.addValue _raw_i8 _raw_i9)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i13) (M.addValue (Litex.denote _value_i14) (Litex.denote _value_i15))) from rfl))
          ))).trans _litex_residual)
        )
    )
  have h_2593 : (by
    let _equal_wd_1_0 := _object_w21
    let _equal_wd_1_1 := _object_w24
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_2608)) + (Litex.NativeBridge.asComplex _value_i14 (Litex.integerToComplex _value_i14 h_2609))) + (Litex.NativeBridge.asComplex _value_i15 (Litex.integerToComplex _value_i15 h_2610))) ((Litex.NativeBridge.asComplex _value_i13 (Litex.integerToComplex _value_i13 h_2608)) + ((Litex.NativeBridge.asComplex _value_i14 (Litex.integerToComplex _value_i14 h_2609)) + (Litex.NativeBridge.asComplex _value_i15 (Litex.integerToComplex _value_i15 h_2610)))) (Litex.NativeBridge.denoteAdd (_object_w21).val.left _value_i15 (_object_w21).wd.1 (_object_w21).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i13 _value_i14 (_object_w16).wd.1 (_object_w16).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_2608)) (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.integerToComplex _value_i14 h_2609))) (Litex.NativeBridge.asComplex_spec _value_i15 (Litex.integerToComplex _value_i15 h_2610))) (Litex.NativeBridge.denoteAdd _value_i13 (_object_w24).val.right (_object_w24).wd.1 (_object_w24).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i13 (Litex.integerToComplex _value_i13 h_2608)) (Litex.NativeBridge.denoteAdd _value_i14 _value_i15 (_object_w18).wd.1 (_object_w18).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i14 (Litex.integerToComplex _value_i14 h_2609)) (Litex.NativeBridge.asComplex_spec _value_i15 (Litex.integerToComplex _value_i15 h_2610)))) (by ring!))
        )
    )
  have h_2594 : (by
    let _equal_wd_1_0 := _object_w19
    let _equal_wd_1_1 := _object_w22
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          ((((((((h_2589).trans h_2590)).trans h_2593)).trans (h_2592).symm)).trans (h_2591).symm)
        )
    )
  exact (And.intro h_2587 (And.intro h_2588 (And.intro h_2589 (And.intro h_2590 (And.intro h_2591 (And.intro h_2592 (And.intro h_2593 h_2594)))))))
);
let h_7038 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Z (M := M)) _set.wd (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Z (M := M)) _set.val.tail.wd (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.emptySubset (Litex.Z (M := M)))))));
Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i7 : M.Value) => True)) h_360 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_362 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i7 : M.Value) => True) i).mpr ⟨h_7038 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_367 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_2595 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))

noncomputable def _object_w44 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => _raw_i10) (by
  intro _raw_i10 h_7056 _
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_7056)
  have h_7056 : Litex.In _value_i10 (Litex.Z (M := M)) := h_7056
  change Litex.In _value_i10 (Litex.Z (M := M))
  exact h_7056));
let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
  intro _raw_i11 _raw_i12 h_7075 h_7076 _
  let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_7075)
  have h_7075 : Litex.In _value_i11 (Litex.Z (M := M)) := h_7075
  let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_7076)
  have h_7076 : Litex.In _value_i12 (Litex.Z (M := M)) := h_7076
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_7075) (Litex.integerToComplex _value_i12 h_7076))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_7075) (Litex.integerToComplex _value_i12 h_7076))
    exact (Litex.addInZ _value_i11 _value_i12 h_7075 h_7076))));
let _wd_1_3 := (Litex.number (M := M) (0 : ℂ));
(let h_7158 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0));
let h_7160 : Litex.In _wd_1_3 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
let h_7165 : ∀ {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_7178 : Litex.In _value_i16 (Litex.Z (M := M))) {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_7179 : Litex.In _value_i17 (Litex.Z (M := M))), (by
  let _object_w28 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_7193 h_7194 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_7193)
    have h_7193 : Litex.In _value_i11 (Litex.Z (M := M)) := h_7193
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_7194)
    have h_7194 : Litex.In _value_i12 (Litex.Z (M := M)) := h_7194
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_7193) (Litex.integerToComplex _value_i12 h_7194))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_7193) (Litex.integerToComplex _value_i12 h_7194))
      exact (Litex.addInZ _value_i11 _value_i12 h_7193 h_7194))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _value_i17;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7178 h_7179 True.intro))
  let _object_w29 := (Litex.add _value_i16 _value_i17 (Litex.integerToComplex _value_i16 h_7178) (Litex.integerToComplex _value_i17 h_7179))
  let _object_w30 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_8293 h_8294 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_8293)
    have h_8293 : Litex.In _value_i11 (Litex.Z (M := M)) := h_8293
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_8294)
    have h_8294 : Litex.In _value_i12 (Litex.Z (M := M)) := h_8294
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_8293) (Litex.integerToComplex _value_i12 h_8294))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_8293) (Litex.integerToComplex _value_i12 h_8294))
      exact (Litex.addInZ _value_i11 _value_i12 h_8293 h_8294))));
  let _wd_2_1 := _value_i17;
  let _wd_2_2 := _value_i16;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7179 h_7178 True.intro))
  let _object_w31 := (Litex.add _value_i17 _value_i16 (Litex.integerToComplex _value_i17 h_7179) (Litex.integerToComplex _value_i16 h_7178))
  exact (((by
    let _equal_wd_1_0 := _object_w28
    let _equal_wd_1_1 := _object_w29
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w30
    let _equal_wd_1_1 := _object_w31
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w29
    let _equal_wd_1_1 := _object_w31
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w28
    let _equal_wd_1_1 := _object_w30
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
) := (by
  intro _Host_i16 _rep_i16 _value_i16 h_7178 _Host_i17 _rep_i17 _value_i17 h_7179
  let _object_w28 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_7193 h_7194 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_7193)
    have h_7193 : Litex.In _value_i11 (Litex.Z (M := M)) := h_7193
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_7194)
    have h_7194 : Litex.In _value_i12 (Litex.Z (M := M)) := h_7194
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_7193) (Litex.integerToComplex _value_i12 h_7194))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_7193) (Litex.integerToComplex _value_i12 h_7194))
      exact (Litex.addInZ _value_i11 _value_i12 h_7193 h_7194))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _value_i17;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7178 h_7179 True.intro))
  let _object_w29 := (Litex.add _value_i16 _value_i17 (Litex.integerToComplex _value_i16 h_7178) (Litex.integerToComplex _value_i17 h_7179))
  have h_7161 : (by
    let _equal_wd_1_0 := _object_w28
    let _equal_wd_1_1 := _object_w29
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (Litex.denote _value_i17)])) = (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) = (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (Litex.denote _value_i17)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (Litex.denote _value_i17)])) = (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
              intro _raw_i11 _raw_i12 h_7932 h_7933 _
              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_7932)
              have h_7932 : Litex.In _value_i11 (Litex.Z (M := M)) := h_7932
              let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_7933)
              have h_7933 : Litex.In _value_i12 (Litex.Z (M := M)) := h_7933
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_7932) (Litex.integerToComplex _value_i12 h_7933))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_7932) (Litex.integerToComplex _value_i12 h_7933))
                exact (Litex.addInZ _value_i11 _value_i12 h_7932 h_7933))));
            let _wd_2_1 := _value_i16;
            let _wd_2_2 := _value_i17;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7178 h_7179 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
              intro _raw_i11 _raw_i12 h_8079 h_8080 _
              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_8079)
              have h_8079 : Litex.In _value_i11 (Litex.Z (M := M)) := h_8079
              let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_8080)
              have h_8080 : Litex.In _value_i12 (Litex.Z (M := M)) := h_8080
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_8079) (Litex.integerToComplex _value_i12 h_8080))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_8079) (Litex.integerToComplex _value_i12 h_8080))
                exact (Litex.addInZ _value_i11 _value_i12 h_8079 h_8080))));
            let _wd_2_1 := _value_i16;
            let _wd_2_2 := _value_i17;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7178 h_7179 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w30 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_8293 h_8294 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_8293)
    have h_8293 : Litex.In _value_i11 (Litex.Z (M := M)) := h_8293
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_8294)
    have h_8294 : Litex.In _value_i12 (Litex.Z (M := M)) := h_8294
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_8293) (Litex.integerToComplex _value_i12 h_8294))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_8293) (Litex.integerToComplex _value_i12 h_8294))
      exact (Litex.addInZ _value_i11 _value_i12 h_8293 h_8294))));
  let _wd_2_1 := _value_i17;
  let _wd_2_2 := _value_i16;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7179 h_7178 True.intro))
  let _object_w31 := (Litex.add _value_i17 _value_i16 (Litex.integerToComplex _value_i17 h_7179) (Litex.integerToComplex _value_i16 h_7178))
  have h_7162 : (by
    let _equal_wd_1_0 := _object_w30
    let _equal_wd_1_1 := _object_w31
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i17), (Litex.denote _value_i16)])) = (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i16)) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i16)) = (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i16)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i17), (Litex.denote _value_i16)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i17), (Litex.denote _value_i16)])) = (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i16)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
              intro _raw_i11 _raw_i12 h_9032 h_9033 _
              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_9032)
              have h_9032 : Litex.In _value_i11 (Litex.Z (M := M)) := h_9032
              let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_9033)
              have h_9033 : Litex.In _value_i12 (Litex.Z (M := M)) := h_9033
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_9032) (Litex.integerToComplex _value_i12 h_9033))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_9032) (Litex.integerToComplex _value_i12 h_9033))
                exact (Litex.addInZ _value_i11 _value_i12 h_9032 h_9033))));
            let _wd_2_1 := _value_i17;
            let _wd_2_2 := _value_i16;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7179 h_7178 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
              intro _raw_i11 _raw_i12 h_9179 h_9180 _
              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_9179)
              have h_9179 : Litex.In _value_i11 (Litex.Z (M := M)) := h_9179
              let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_9180)
              have h_9180 : Litex.In _value_i12 (Litex.Z (M := M)) := h_9180
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_9179) (Litex.integerToComplex _value_i12 h_9180))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_9179) (Litex.integerToComplex _value_i12 h_9180))
                exact (Litex.addInZ _value_i11 _value_i12 h_9179 h_9180))));
            let _wd_2_1 := _value_i17;
            let _wd_2_2 := _value_i16;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_7179 h_7178 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i16)) from rfl))
          ))).trans _litex_residual)
        )
    )
  have h_7163 : (by
    let _equal_wd_1_0 := _object_w29
    let _equal_wd_1_1 := _object_w31
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i16 (Litex.integerToComplex _value_i16 h_7178)) + (Litex.NativeBridge.asComplex _value_i17 (Litex.integerToComplex _value_i17 h_7179))) ((Litex.NativeBridge.asComplex _value_i17 (Litex.integerToComplex _value_i17 h_7179)) + (Litex.NativeBridge.asComplex _value_i16 (Litex.integerToComplex _value_i16 h_7178))) (Litex.NativeBridge.denoteAdd _value_i16 _value_i17 (_object_w29).wd.1 (_object_w29).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.integerToComplex _value_i16 h_7178)) (Litex.NativeBridge.asComplex_spec _value_i17 (Litex.integerToComplex _value_i17 h_7179))) (Litex.NativeBridge.denoteAdd _value_i17 _value_i16 (_object_w31).wd.1 (_object_w31).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i17 (Litex.integerToComplex _value_i17 h_7179)) (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.integerToComplex _value_i16 h_7178))) (by ring!))
        )
    )
  have h_7164 : (by
    let _equal_wd_1_0 := _object_w28
    let _equal_wd_1_1 := _object_w30
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          ((((h_7161).trans h_7163)).trans (h_7162).symm)
        )
    )
  exact (And.intro h_7161 (And.intro h_7162 (And.intro h_7163 h_7164)))
);
let h_9393 : ∀ {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_9406 : Litex.In _value_i16 (Litex.Z (M := M))) {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_9407 : Litex.In _value_i17 (Litex.Z (M := M))) {_Host_i18 : Type _} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_9408 : Litex.In _value_i18 (Litex.Z (M := M))), (by
  let _object_w33 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_9422 h_9423 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_9422)
    have h_9422 : Litex.In _value_i11 (Litex.Z (M := M)) := h_9422
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_9423)
    have h_9423 : Litex.In _value_i12 (Litex.Z (M := M)) := h_9423
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_9422) (Litex.integerToComplex _value_i12 h_9423))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_9422) (Litex.integerToComplex _value_i12 h_9423))
      exact (Litex.addInZ _value_i11 _value_i12 h_9422 h_9423))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _value_i17;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9406 h_9407 True.intro))
  let _object_w34 := (Litex.add _value_i16 _value_i17 (Litex.integerToComplex _value_i16 h_9406) (Litex.integerToComplex _value_i17 h_9407))
  let _object_w35 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_10686 h_10687 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_10686)
    have h_10686 : Litex.In _value_i11 (Litex.Z (M := M)) := h_10686
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_10687)
    have h_10687 : Litex.In _value_i12 (Litex.Z (M := M)) := h_10687
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_10686) (Litex.integerToComplex _value_i12 h_10687))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_10686) (Litex.integerToComplex _value_i12 h_10687))
      exact (Litex.addInZ _value_i11 _value_i12 h_10686 h_10687))));
  let _wd_2_1 := _value_i17;
  let _wd_2_2 := _value_i18;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9407 h_9408 True.intro))
  let _object_w36 := (Litex.add _value_i17 _value_i18 (Litex.integerToComplex _value_i17 h_9407) (Litex.integerToComplex _value_i18 h_9408))
  let _object_w37 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_11978 h_11979 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_11978)
    have h_11978 : Litex.In _value_i11 (Litex.Z (M := M)) := h_11978
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_11979)
    have h_11979 : Litex.In _value_i12 (Litex.Z (M := M)) := h_11979
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_11978) (Litex.integerToComplex _value_i12 h_11979))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_11978) (Litex.integerToComplex _value_i12 h_11979))
      exact (Litex.addInZ _value_i11 _value_i12 h_11978 h_11979))));
  let _wd_2_1 := _object_w33;
  let _wd_2_2 := _value_i18;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w33
    exact (Litex.inOfSame _object_w33 _object_w33 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w33) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w33))) h_9408 True.intro))
  let _object_w38 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_12180 h_12181 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_12180)
    have h_12180 : Litex.In _value_i11 (Litex.Z (M := M)) := h_12180
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_12181)
    have h_12181 : Litex.In _value_i12 (Litex.Z (M := M)) := h_12181
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_12180) (Litex.integerToComplex _value_i12 h_12181))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_12180) (Litex.integerToComplex _value_i12 h_12181))
      exact (Litex.addInZ _value_i11 _value_i12 h_12180 h_12181))));
  let _wd_2_1 := _object_w34;
  let _wd_2_2 := _value_i18;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w34
    exact (Litex.addInZ _value_i16 _value_i17 h_9406 h_9407)) h_9408 True.intro))
  let _object_w39 := (let _wd_2_0 := _object_w34;
  let _wd_2_1 := _value_i18;
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _object_w34
    exact (Litex.addInC _value_i16 _value_i17 (Litex.integerToComplex _value_i16 h_9406) (Litex.integerToComplex _value_i17 h_9407))) (Litex.integerToComplex _wd_2_1 h_9408)))
  let _object_w40 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_12914 h_12915 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_12914)
    have h_12914 : Litex.In _value_i11 (Litex.Z (M := M)) := h_12914
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_12915)
    have h_12915 : Litex.In _value_i12 (Litex.Z (M := M)) := h_12915
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_12914) (Litex.integerToComplex _value_i12 h_12915))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_12914) (Litex.integerToComplex _value_i12 h_12915))
      exact (Litex.addInZ _value_i11 _value_i12 h_12914 h_12915))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _object_w35;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9406 (by
    let _atomic_wd_1_0 := _object_w35
    exact (Litex.inOfSame _object_w35 _object_w35 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w35) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w35))) True.intro))
  let _object_w41 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_13112 h_13113 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_13112)
    have h_13112 : Litex.In _value_i11 (Litex.Z (M := M)) := h_13112
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_13113)
    have h_13113 : Litex.In _value_i12 (Litex.Z (M := M)) := h_13113
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_13112) (Litex.integerToComplex _value_i12 h_13113))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_13112) (Litex.integerToComplex _value_i12 h_13113))
      exact (Litex.addInZ _value_i11 _value_i12 h_13112 h_13113))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _object_w36;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9406 (by
    let _atomic_wd_1_0 := _object_w36
    exact (Litex.addInZ _value_i17 _value_i18 h_9407 h_9408)) True.intro))
  let _object_w42 := (let _wd_2_0 := _value_i16;
  let _wd_2_1 := _object_w36;
  (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_9406) (by
    let _atomic_wd_1_0 := _object_w36
    exact (Litex.addInC _value_i17 _value_i18 (Litex.integerToComplex _value_i17 h_9407) (Litex.integerToComplex _value_i18 h_9408)))))
  exact (((by
    let _equal_wd_1_0 := _object_w33
    let _equal_wd_1_1 := _object_w34
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w35
    let _equal_wd_1_1 := _object_w36
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w37
    let _equal_wd_1_1 := _object_w38
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w38
    let _equal_wd_1_1 := _object_w39
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w40
    let _equal_wd_1_1 := _object_w41
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w41
    let _equal_wd_1_1 := _object_w42
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w39
    let _equal_wd_1_1 := _object_w42
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w37
    let _equal_wd_1_1 := _object_w40
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
) := (by
  intro _Host_i16 _rep_i16 _value_i16 h_9406 _Host_i17 _rep_i17 _value_i17 h_9407 _Host_i18 _rep_i18 _value_i18 h_9408
  let _object_w33 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_9422 h_9423 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_9422)
    have h_9422 : Litex.In _value_i11 (Litex.Z (M := M)) := h_9422
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_9423)
    have h_9423 : Litex.In _value_i12 (Litex.Z (M := M)) := h_9423
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_9422) (Litex.integerToComplex _value_i12 h_9423))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_9422) (Litex.integerToComplex _value_i12 h_9423))
      exact (Litex.addInZ _value_i11 _value_i12 h_9422 h_9423))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _value_i17;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9406 h_9407 True.intro))
  let _object_w34 := (Litex.add _value_i16 _value_i17 (Litex.integerToComplex _value_i16 h_9406) (Litex.integerToComplex _value_i17 h_9407))
  have h_9385 : (by
    let _equal_wd_1_0 := _object_w33
    let _equal_wd_1_1 := _object_w34
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (Litex.denote _value_i17)])) = (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) = (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (Litex.denote _value_i17)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (Litex.denote _value_i17)])) = (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
              intro _raw_i11 _raw_i12 h_10269 h_10270 _
              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_10269)
              have h_10269 : Litex.In _value_i11 (Litex.Z (M := M)) := h_10269
              let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_10270)
              have h_10270 : Litex.In _value_i12 (Litex.Z (M := M)) := h_10270
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_10269) (Litex.integerToComplex _value_i12 h_10270))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_10269) (Litex.integerToComplex _value_i12 h_10270))
                exact (Litex.addInZ _value_i11 _value_i12 h_10269 h_10270))));
            let _wd_2_1 := _value_i16;
            let _wd_2_2 := _value_i17;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9406 h_9407 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
              intro _raw_i11 _raw_i12 h_10436 h_10437 _
              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_10436)
              have h_10436 : Litex.In _value_i11 (Litex.Z (M := M)) := h_10436
              let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_10437)
              have h_10437 : Litex.In _value_i12 (Litex.Z (M := M)) := h_10437
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_10436) (Litex.integerToComplex _value_i12 h_10437))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_10436) (Litex.integerToComplex _value_i12 h_10437))
                exact (Litex.addInZ _value_i11 _value_i12 h_10436 h_10437))));
            let _wd_2_1 := _value_i16;
            let _wd_2_2 := _value_i17;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9406 h_9407 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w35 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_10686 h_10687 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_10686)
    have h_10686 : Litex.In _value_i11 (Litex.Z (M := M)) := h_10686
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_10687)
    have h_10687 : Litex.In _value_i12 (Litex.Z (M := M)) := h_10687
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_10686) (Litex.integerToComplex _value_i12 h_10687))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_10686) (Litex.integerToComplex _value_i12 h_10687))
      exact (Litex.addInZ _value_i11 _value_i12 h_10686 h_10687))));
  let _wd_2_1 := _value_i17;
  let _wd_2_2 := _value_i18;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9407 h_9408 True.intro))
  let _object_w36 := (Litex.add _value_i17 _value_i18 (Litex.integerToComplex _value_i17 h_9407) (Litex.integerToComplex _value_i18 h_9408))
  have h_9386 : (by
    let _equal_wd_1_0 := _object_w35
    let _equal_wd_1_1 := _object_w36
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i17), (Litex.denote _value_i18)])) = (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i18)) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i18)) = (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i18)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i17), (Litex.denote _value_i18)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i17), (Litex.denote _value_i18)])) = (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i18)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
              intro _raw_i11 _raw_i12 h_11553 h_11554 _
              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_11553)
              have h_11553 : Litex.In _value_i11 (Litex.Z (M := M)) := h_11553
              let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_11554)
              have h_11554 : Litex.In _value_i12 (Litex.Z (M := M)) := h_11554
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_11553) (Litex.integerToComplex _value_i12 h_11554))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_11553) (Litex.integerToComplex _value_i12 h_11554))
                exact (Litex.addInZ _value_i11 _value_i12 h_11553 h_11554))));
            let _wd_2_1 := _value_i17;
            let _wd_2_2 := _value_i18;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9407 h_9408 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
              intro _raw_i11 _raw_i12 h_11724 h_11725 _
              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_11724)
              have h_11724 : Litex.In _value_i11 (Litex.Z (M := M)) := h_11724
              let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_11725)
              have h_11725 : Litex.In _value_i12 (Litex.Z (M := M)) := h_11725
              change (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_11724) (Litex.integerToComplex _value_i12 h_11725))
                exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_11724) (Litex.integerToComplex _value_i12 h_11725))
                exact (Litex.addInZ _value_i11 _value_i12 h_11724 h_11725))));
            let _wd_2_1 := _value_i17;
            let _wd_2_2 := _value_i18;
            (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9407 h_9408 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i18)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w37 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_11978 h_11979 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_11978)
    have h_11978 : Litex.In _value_i11 (Litex.Z (M := M)) := h_11978
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_11979)
    have h_11979 : Litex.In _value_i12 (Litex.Z (M := M)) := h_11979
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_11978) (Litex.integerToComplex _value_i12 h_11979))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_11978) (Litex.integerToComplex _value_i12 h_11979))
      exact (Litex.addInZ _value_i11 _value_i12 h_11978 h_11979))));
  let _wd_2_1 := _object_w33;
  let _wd_2_2 := _value_i18;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w33
    exact (Litex.inOfSame _object_w33 _object_w33 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w33) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w33))) h_9408 True.intro))
  let _object_w38 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_12180 h_12181 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_12180)
    have h_12180 : Litex.In _value_i11 (Litex.Z (M := M)) := h_12180
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_12181)
    have h_12181 : Litex.In _value_i12 (Litex.Z (M := M)) := h_12181
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_12180) (Litex.integerToComplex _value_i12 h_12181))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_12180) (Litex.integerToComplex _value_i12 h_12181))
      exact (Litex.addInZ _value_i11 _value_i12 h_12180 h_12181))));
  let _wd_2_1 := _object_w34;
  let _wd_2_2 := _value_i18;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w34
    exact (Litex.addInZ _value_i16 _value_i17 h_9406 h_9407)) h_9408 True.intro))
  have h_9387 : (by
    let _equal_wd_1_0 := _object_w37
    let _equal_wd_1_1 := _object_w38
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_9385 (show @Eq M.Value _ _ from Eq.refl _)))
        )
    )
  let _object_w39 := (let _wd_2_0 := _object_w34;
  let _wd_2_1 := _value_i18;
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _object_w34
    exact (Litex.addInC _value_i16 _value_i17 (Litex.integerToComplex _value_i16 h_9406) (Litex.integerToComplex _value_i17 h_9407))) (Litex.integerToComplex _wd_2_1 h_9408)))
  have h_9388 : (by
    let _equal_wd_1_0 := _object_w38
    let _equal_wd_1_1 := _object_w39
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)), (Litex.denote _value_i18)])) = (M.addValue (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) (Litex.denote _value_i18)) from by
            have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) (Litex.denote _value_i18)) = (M.addValue (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) (Litex.denote _value_i18)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)), (Litex.denote _value_i18)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)), (Litex.denote _value_i18)])) = (M.addValue (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) (Litex.denote _value_i18)) from by
            let _litex_original := _object_w38
            let _litex_literal := _object_w38
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (Litex.denote _value_i16) (Litex.denote _value_i17)) (Litex.denote _value_i18)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w40 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_12914 h_12915 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_12914)
    have h_12914 : Litex.In _value_i11 (Litex.Z (M := M)) := h_12914
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_12915)
    have h_12915 : Litex.In _value_i12 (Litex.Z (M := M)) := h_12915
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_12914) (Litex.integerToComplex _value_i12 h_12915))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_12914) (Litex.integerToComplex _value_i12 h_12915))
      exact (Litex.addInZ _value_i11 _value_i12 h_12914 h_12915))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _object_w35;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9406 (by
    let _atomic_wd_1_0 := _object_w35
    exact (Litex.inOfSame _object_w35 _object_w35 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _object_w35) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _object_w35))) True.intro))
  let _object_w41 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by
    intro _raw_i11 _raw_i12 h_13112 h_13113 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_13112)
    have h_13112 : Litex.In _value_i11 (Litex.Z (M := M)) := h_13112
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_13113)
    have h_13113 : Litex.In _value_i12 (Litex.Z (M := M)) := h_13113
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_13112) (Litex.integerToComplex _value_i12 h_13113))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i11 _value_i12 (Litex.integerToComplex _value_i11 h_13112) (Litex.integerToComplex _value_i12 h_13113))
      exact (Litex.addInZ _value_i11 _value_i12 h_13112 h_13113))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _object_w36;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_9406 (by
    let _atomic_wd_1_0 := _object_w36
    exact (Litex.addInZ _value_i17 _value_i18 h_9407 h_9408)) True.intro))
  have h_9389 : (by
    let _equal_wd_1_0 := _object_w40
    let _equal_wd_1_1 := _object_w41
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_9386))
        )
    )
  let _object_w42 := (let _wd_2_0 := _value_i16;
  let _wd_2_1 := _object_w36;
  (Litex.add _wd_2_0 _wd_2_1 (Litex.integerToComplex _wd_2_0 h_9406) (by
    let _atomic_wd_1_0 := _object_w36
    exact (Litex.addInC _value_i17 _value_i18 (Litex.integerToComplex _value_i17 h_9407) (Litex.integerToComplex _value_i18 h_9408)))))
  have h_9390 : (by
    let _equal_wd_1_0 := _object_w41
    let _equal_wd_1_1 := _object_w42
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i18))])) = (M.addValue (Litex.denote _value_i16) (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i18))) from by
            have _litex_residual : (M.addValue (Litex.denote _value_i16) (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i18))) = (M.addValue (Litex.denote _value_i16) (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i18))) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i18))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.integer), (M.standard Litex.StandardSetValue.integer)]) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.integer) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i18))])) = (M.addValue (Litex.denote _value_i16) (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i18))) from by
            let _litex_original := _object_w41
            let _litex_literal := _object_w41
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i11 : M.Value) (_raw_i12 : M.Value) => (M.addValue _raw_i11 _raw_i12)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (Litex.denote _value_i16) (M.addValue (Litex.denote _value_i17) (Litex.denote _value_i18))) from rfl))
          ))).trans _litex_residual)
        )
    )
  have h_9391 : (by
    let _equal_wd_1_0 := _object_w39
    let _equal_wd_1_1 := _object_w42
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i16 (Litex.integerToComplex _value_i16 h_9406)) + (Litex.NativeBridge.asComplex _value_i17 (Litex.integerToComplex _value_i17 h_9407))) + (Litex.NativeBridge.asComplex _value_i18 (Litex.integerToComplex _value_i18 h_9408))) ((Litex.NativeBridge.asComplex _value_i16 (Litex.integerToComplex _value_i16 h_9406)) + ((Litex.NativeBridge.asComplex _value_i17 (Litex.integerToComplex _value_i17 h_9407)) + (Litex.NativeBridge.asComplex _value_i18 (Litex.integerToComplex _value_i18 h_9408)))) (Litex.NativeBridge.denoteAdd (_object_w39).val.left _value_i18 (_object_w39).wd.1 (_object_w39).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i16 _value_i17 (_object_w34).wd.1 (_object_w34).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.integerToComplex _value_i16 h_9406)) (Litex.NativeBridge.asComplex_spec _value_i17 (Litex.integerToComplex _value_i17 h_9407))) (Litex.NativeBridge.asComplex_spec _value_i18 (Litex.integerToComplex _value_i18 h_9408))) (Litex.NativeBridge.denoteAdd _value_i16 (_object_w42).val.right (_object_w42).wd.1 (_object_w42).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.integerToComplex _value_i16 h_9406)) (Litex.NativeBridge.denoteAdd _value_i17 _value_i18 (_object_w36).wd.1 (_object_w36).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i17 (Litex.integerToComplex _value_i17 h_9407)) (Litex.NativeBridge.asComplex_spec _value_i18 (Litex.integerToComplex _value_i18 h_9408)))) (by ring!))
        )
    )
  have h_9392 : (by
    let _equal_wd_1_0 := _object_w37
    let _equal_wd_1_1 := _object_w40
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          ((((((((h_9387).trans h_9388)).trans h_9391)).trans (h_9390).symm)).trans (h_9389).symm)
        )
    )
  exact (And.intro h_9385 (And.intro h_9386 (And.intro h_9387 (And.intro h_9388 (And.intro h_9389 (And.intro h_9390 (And.intro h_9391 h_9392)))))))
);
let h_13836 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Z (M := M)) _set.wd (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Z (M := M)) _set.val.tail.wd (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.emptySubset (Litex.Z (M := M)))))));
Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True)) h_7158 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_7160 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i10 : M.Value) => True) i).mpr ⟨h_13836 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_7165 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_9393 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))

theorem h_243 : (by
  let _equal_wd_1_0 := (_object_w43 (M := M))
  let _equal_wd_1_1 := (_object_w44 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w43 (M := M));
        let _equal_wd_1_1 := (_object_w44 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
          let _left := _equal_wd_1_0
          let _right := _equal_wd_1_1
          exact (show Litex.Same _left _right from rfl))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_fold_x5f_bound_x5f_names_x2f_statement_x2e_lit
