import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_fold_x5f_guarded_x5f_literal_x2f_statement_x2e_lit

universe u v1 v3 v6 v7 v8 v9 v10 v11
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_8 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_64 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
    intro _raw_i2 h_63 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_63)
    have h_63 : Litex.In _value_i2 (Litex.Z (M := M)) := h_63
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i2 = (M.number (0 : ℂ))))
              exact h_1)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_67 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.integer) → M.mem _raw_i5 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → True := (by
    intro _raw_i4 _raw_i5 h_65 h_66 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_65)
    have h_65 : Litex.In _value_i4 (Litex.Z (M := M)) := h_65
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_66)
    have h_66 : Litex.In _value_i5 (Litex.Z (M := M)) := h_66
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_68 : Litex.In _value_i6 (Litex.Z (M := M))) (h_3 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_69 : Litex.In _value_i7 (Litex.Z (M := M))) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_70 : Litex.In _value_i8 (Litex.Z (M := M))), (by
  let _equal_wd_1_0 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _value_i3 _value_i7 _value_i8 h_67 h_69 h_70 True.intro)
  let _equal_wd_1_1 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _value_i3 _value_i8 _value_i7 h_67 h_70 h_69 True.intro)
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) (h_5 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_95 : Litex.In _value_i9 (Litex.Z (M := M))) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_96 : Litex.In _value_i10 (Litex.Z (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_97 : Litex.In _value_i11 (Litex.Z (M := M))), (by
  let _equal_wd_1_0 := (let _object_w25 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _value_i3 _value_i9 _value_i10 h_67 h_95 h_96 True.intro);
  let _wd_1_1 := _value_i11;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _value_i3 _object_w25 _wd_1_1 h_67 (by
    let _atomic_wd_1_0 := _object_w25
    exact (by
      let _litex_return_call := _object_w25
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_97 True.intro))
  let _equal_wd_1_1 := (let _wd_1_0 := _value_i9;
  let _object_w26 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _value_i3 _value_i10 _value_i11 h_67 h_96 h_97 True.intro);
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _value_i3 _wd_1_0 _object_w26 h_67 h_95 (by
    let _atomic_wd_1_0 := _object_w26
    exact (by
      let _litex_return_call := _object_w26
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), (by
  let _object_w29 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  let _wd_1_1 := _value_i1;
  let _wd_1_2 := _value_i3;
  let _wd_1_3 := _value_i6;
  (let h_277 : (by
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
  let h_279 : Litex.In _wd_1_3 (Litex.Z (M := M)) := h_68;
  let h_289 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_291 : Litex.In _value_i12 (Litex.Z (M := M))) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_292 : Litex.In _value_i13 (Litex.Z (M := M))), Litex.Same (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 h_67 h_291 h_292 True.intro) (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i12 h_67 h_292 h_291 True.intro) := (by
    intro _Host_i12 _rep_i12 _value_i12 h_291 _Host_i13 _rep_i13 _value_i13 h_292
    exact (h_3 _value_i12 h_291 _value_i13 h_292)
  );
  let h_318 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_320 : Litex.In _value_i12 (Litex.Z (M := M))) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_321 : Litex.In _value_i13 (Litex.Z (M := M))) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_322 : Litex.In _value_i14 (Litex.Z (M := M))), Litex.Same (let _object_w27 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 h_67 h_320 h_321 True.intro);
  let _wd_2_1 := _value_i14;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _object_w27 _wd_2_1 h_67 (by
    let _atomic_wd_1_0 := _object_w27
    exact (by
      let _litex_return_call := _object_w27
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_322 True.intro)) (let _wd_2_0 := _value_i12;
  let _object_w28 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i14 h_67 h_321 h_322 True.intro);
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _object_w28 h_67 h_320 (by
    let _atomic_wd_1_0 := _object_w28
    exact (by
      let _litex_return_call := _object_w28
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro)) := (by
    intro _Host_i12 _rep_i12 _value_i12 h_320 _Host_i13 _rep_i13 _value_i13 h_321 _Host_i14 _rep_i14 _value_i14 h_322
    exact (h_5 _value_i12 h_320 _value_i13 h_321 _value_i14 h_322)
  );
  let h_501 : (by
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
  let h_517 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
  let h_518 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
  let _fold_tail_0 := _wd_1_0;
  let _fold_tail_1 := _fold_tail_0.val.tail;
  let _fold_tail_2 := _fold_tail_1.val.tail;
  let _fold_guard : ∀ i, M.mem i (Litex.denote _wd_1_0) → (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) i := Litex.finiteGuardInsert _fold_tail_0 (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (h_517) (Litex.finiteGuardInsert _fold_tail_1 (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (h_518) (Litex.finiteGuardEmpty (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))));
  Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) h_277 (Litex.inOfSame _wd_1_1 _wd_1_1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.sameRefl _wd_1_1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))) h_64) (Litex.inOfSame _wd_1_2 _wd_1_2 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _wd_1_2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) h_67) h_279 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) i).mpr ⟨h_501 i hi, _fold_guard i hi⟩) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (h_289 _fold_x0 _fold_h0 _fold_x1 _fold_h1))))) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (h_318 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2)))))))))
  let _object_w34 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0);
  let _wd_1_1 := _value_i1;
  let _wd_1_2 := _value_i3;
  let _wd_1_3 := _value_i6;
  (let h_559 : (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact (let _finite_tail_0 := _atomic_wd_1_0;
    have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
    _finite_0));
  let h_560 : Litex.In _wd_1_3 (Litex.Z (M := M)) := h_68;
  let h_570 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_572 : Litex.In _value_i15 (Litex.Z (M := M))) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_573 : Litex.In _value_i16 (Litex.Z (M := M))), Litex.Same (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i15 _value_i16 h_67 h_572 h_573 True.intro) (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i16 _value_i15 h_67 h_573 h_572 True.intro) := (by
    intro _Host_i15 _rep_i15 _value_i15 h_572 _Host_i16 _rep_i16 _value_i16 h_573
    exact (h_3 _value_i15 h_572 _value_i16 h_573)
  );
  let h_599 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_601 : Litex.In _value_i15 (Litex.Z (M := M))) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_602 : Litex.In _value_i16 (Litex.Z (M := M))) {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_603 : Litex.In _value_i17 (Litex.Z (M := M))), Litex.Same (let _object_w30 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i15 _value_i16 h_67 h_601 h_602 True.intro);
  let _wd_2_1 := _value_i17;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _object_w30 _wd_2_1 h_67 (by
    let _atomic_wd_1_0 := _object_w30
    exact (by
      let _litex_return_call := _object_w30
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_603 True.intro)) (let _wd_2_0 := _value_i15;
  let _object_w31 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i16 _value_i17 h_67 h_602 h_603 True.intro);
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _object_w31 h_67 h_601 (by
    let _atomic_wd_1_0 := _object_w31
    exact (by
      let _litex_return_call := _object_w31
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro)) := (by
    intro _Host_i15 _rep_i15 _value_i15 h_601 _Host_i16 _rep_i16 _value_i16 h_602 _Host_i17 _rep_i17 _value_i17 h_603
    exact (h_5 _value_i15 h_601 _value_i16 h_602 _value_i17 h_603)
  );
  let h_802 : (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact (by
      let _set := _atomic_wd_1_0
      exact (Litex.emptySubset (Litex.Z (M := M)))));
  let _fold_tail_0 := _wd_1_0;
  let _fold_guard : ∀ i, M.mem i (Litex.denote _wd_1_0) → (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) i := Litex.finiteGuardEmpty (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))));
  Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) h_559 (Litex.inOfSame _wd_1_1 _wd_1_1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.sameRefl _wd_1_1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))) h_64) (Litex.inOfSame _wd_1_2 _wd_1_2 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _wd_1_2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) h_67) h_560 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) i).mpr ⟨h_802 i hi, _fold_guard i hi⟩) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (h_570 _fold_x0 _fold_h0 _fold_x1 _fold_h1))))) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (h_599 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2)))))))))
  exact (((by
    let _atomic_wd_1_0 := _object_w29
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))) ∧ ((by
    let _equal_wd_1_0 := _object_w34
    exact Litex.Same _equal_wd_1_0 _value_i6)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_64 _Host_i3 _rep_i3 _value_i3 h_67 _Host_i6 _rep_i6 _value_i6 h_68 h_3 h_5
          let _object_w29 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_1_1 := _value_i1;
          let _wd_1_2 := _value_i3;
          let _wd_1_3 := _value_i6;
          (let h_277 : (by
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
          let h_279 : Litex.In _wd_1_3 (Litex.Z (M := M)) := h_68;
          let h_289 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_291 : Litex.In _value_i12 (Litex.Z (M := M))) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_292 : Litex.In _value_i13 (Litex.Z (M := M))), Litex.Same (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 h_67 h_291 h_292 True.intro) (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i12 h_67 h_292 h_291 True.intro) := (by
            intro _Host_i12 _rep_i12 _value_i12 h_291 _Host_i13 _rep_i13 _value_i13 h_292
            exact (h_3 _value_i12 h_291 _value_i13 h_292)
          );
          let h_318 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_320 : Litex.In _value_i12 (Litex.Z (M := M))) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_321 : Litex.In _value_i13 (Litex.Z (M := M))) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_322 : Litex.In _value_i14 (Litex.Z (M := M))), Litex.Same (let _object_w27 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i12 _value_i13 h_67 h_320 h_321 True.intro);
          let _wd_2_1 := _value_i14;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _object_w27 _wd_2_1 h_67 (by
            let _atomic_wd_1_0 := _object_w27
            exact (by
              let _litex_return_call := _object_w27
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_322 True.intro)) (let _wd_2_0 := _value_i12;
          let _object_w28 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i13 _value_i14 h_67 h_321 h_322 True.intro);
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _object_w28 h_67 h_320 (by
            let _atomic_wd_1_0 := _object_w28
            exact (by
              let _litex_return_call := _object_w28
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro)) := (by
            intro _Host_i12 _rep_i12 _value_i12 h_320 _Host_i13 _rep_i13 _value_i13 h_321 _Host_i14 _rep_i14 _value_i14 h_322
            exact (h_5 _value_i12 h_320 _value_i13 h_321 _value_i14 h_322)
          );
          let h_501 : (by
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
          let h_517 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
          let h_518 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
          let _fold_tail_0 := _wd_1_0;
          let _fold_tail_1 := _fold_tail_0.val.tail;
          let _fold_tail_2 := _fold_tail_1.val.tail;
          let _fold_guard : ∀ i, M.mem i (Litex.denote _wd_1_0) → (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) i := Litex.finiteGuardInsert _fold_tail_0 (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (h_517) (Litex.finiteGuardInsert _fold_tail_1 (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (h_518) (Litex.finiteGuardEmpty (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))));
          Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) h_277 (Litex.inOfSame _wd_1_1 _wd_1_1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.sameRefl _wd_1_1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))) h_64) (Litex.inOfSame _wd_1_2 _wd_1_2 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _wd_1_2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) h_67) h_279 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) i).mpr ⟨h_501 i hi, _fold_guard i hi⟩) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (h_289 _fold_x0 _fold_h0 _fold_x1 _fold_h1))))) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (h_318 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2)))))))))
          have h_6 : (by
            let _atomic_wd_1_0 := _object_w29
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w29
                    exact (by
                      have _selected_operation : Litex.In _value_i3 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) := h_67
                      exact Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _atomic_wd_1_0) (Litex.sameRefl (Litex.Z (M := M))) (Litex.finiteFoldInOutput _atomic_wd_1_0)))
                )
            )
          let _object_w34 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0);
          let _wd_1_1 := _value_i1;
          let _wd_1_2 := _value_i3;
          let _wd_1_3 := _value_i6;
          (let h_559 : (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact (let _finite_tail_0 := _atomic_wd_1_0;
            have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
            _finite_0));
          let h_560 : Litex.In _wd_1_3 (Litex.Z (M := M)) := h_68;
          let h_570 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_572 : Litex.In _value_i15 (Litex.Z (M := M))) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_573 : Litex.In _value_i16 (Litex.Z (M := M))), Litex.Same (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i15 _value_i16 h_67 h_572 h_573 True.intro) (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i16 _value_i15 h_67 h_573 h_572 True.intro) := (by
            intro _Host_i15 _rep_i15 _value_i15 h_572 _Host_i16 _rep_i16 _value_i16 h_573
            exact (h_3 _value_i15 h_572 _value_i16 h_573)
          );
          let h_599 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_601 : Litex.In _value_i15 (Litex.Z (M := M))) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_602 : Litex.In _value_i16 (Litex.Z (M := M))) {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_603 : Litex.In _value_i17 (Litex.Z (M := M))), Litex.Same (let _object_w30 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i15 _value_i16 h_67 h_601 h_602 True.intro);
          let _wd_2_1 := _value_i17;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _object_w30 _wd_2_1 h_67 (by
            let _atomic_wd_1_0 := _object_w30
            exact (by
              let _litex_return_call := _object_w30
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_603 True.intro)) (let _wd_2_0 := _value_i15;
          let _object_w31 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _value_i16 _value_i17 h_67 h_602 h_603 True.intro);
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_2 _wd_2_0 _object_w31 h_67 h_601 (by
            let _atomic_wd_1_0 := _object_w31
            exact (by
              let _litex_return_call := _object_w31
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro)) := (by
            intro _Host_i15 _rep_i15 _value_i15 h_601 _Host_i16 _rep_i16 _value_i16 h_602 _Host_i17 _rep_i17 _value_i17 h_603
            exact (h_5 _value_i15 h_601 _value_i16 h_602 _value_i17 h_603)
          );
          let h_802 : (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact Litex.Subset _atomic_wd_1_0 (Litex.Z (M := M))) := (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact (by
              let _set := _atomic_wd_1_0
              exact (Litex.emptySubset (Litex.Z (M := M)))));
          let _fold_tail_0 := _wd_1_0;
          let _fold_guard : ∀ i, M.mem i (Litex.denote _wd_1_0) → (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) i := Litex.finiteGuardEmpty (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))));
          Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) h_559 (Litex.inOfSame _wd_1_1 _wd_1_1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.sameRefl _wd_1_1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))) h_64) (Litex.inOfSame _wd_1_2 _wd_1_2 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _wd_1_2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) h_67) h_560 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) i).mpr ⟨h_802 i hi, _fold_guard i hi⟩) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (h_570 _fold_x0 _fold_h0 _fold_x1 _fold_h1))))) (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (h_599 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2)))))))))
          have h_7 : (by
            let _equal_wd_1_0 := _object_w34
            exact Litex.Same _equal_wd_1_0 _value_i6) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w34;
                  (show Litex.Same _equal_wd_1_0 _value_i6 from ((Litex.finiteFoldEmpty _equal_wd_1_0 rfl))))
                )
            )
          exact (And.intro h_6 h_7)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_fold_x5f_guarded_x5f_literal_x2f_statement_x2e_lit
