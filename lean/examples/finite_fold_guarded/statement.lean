import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_fold_x5f_guarded_x2f_statement_x2e_lit

universe u v1 v2 v4 v7 v8 v9 v10 v11 v12 v13
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_10 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_65 : Litex.IsFiniteSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_67 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) _raw_i3) → True := (by
    intro _raw_i3 h_66 h_1
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_66)
    have h_66 : Litex.In _value_i3 (Litex.Z (M := M)) := h_66
    have h_1 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i3 = (M.number (0 : ℂ))))
              exact h_1)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_70 : Litex.In _value_i4 (let _checked_header : ∀ (_raw_i5 : M.Value) (_raw_i6 : M.Value), M.mem _raw_i5 (M.standard Litex.StandardSetValue.integer) → M.mem _raw_i6 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _raw_i5 _raw_i6) → True := (by
    intro _raw_i5 _raw_i6 h_68 h_69 _
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_68)
    have h_68 : Litex.In _value_i5 (Litex.Z (M := M)) := h_68
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_69)
    have h_69 : Litex.In _value_i6 (Litex.Z (M := M)) := h_69
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True)))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_71 : Litex.In _value_i7 (Litex.Z (M := M))) (h_2 : Litex.Subset _value_i1 (Litex.Z (M := M))) (h_4 : ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_79 : Litex.In _value_i8 _value_i1), ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ))) (h_6 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_80 : Litex.In _value_i9 (Litex.Z (M := M))) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_81 : Litex.In _value_i10 (Litex.Z (M := M))), (by
  let _equal_wd_1_0 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _value_i9 _value_i10 h_70 h_80 h_81 True.intro)
  let _equal_wd_1_1 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _value_i10 _value_i9 h_70 h_81 h_80 True.intro)
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) (h_8 : ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_106 : Litex.In _value_i11 (Litex.Z (M := M))) {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_107 : Litex.In _value_i12 (Litex.Z (M := M))) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_108 : Litex.In _value_i13 (Litex.Z (M := M))), (by
  let _equal_wd_1_0 := (let _object_w25 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _value_i11 _value_i12 h_70 h_106 h_107 True.intro);
  let _wd_1_1 := _value_i13;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _object_w25 _wd_1_1 h_70 (by
    let _atomic_wd_1_0 := _object_w25
    exact (by
      let _litex_return_call := _object_w25
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_108 True.intro))
  let _equal_wd_1_1 := (let _wd_1_0 := _value_i11;
  let _object_w26 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _value_i12 _value_i13 h_70 h_107 h_108 True.intro);
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _wd_1_0 _object_w26 h_70 h_106 (by
    let _atomic_wd_1_0 := _object_w26
    exact (by
      let _litex_return_call := _object_w26
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), (by
  let _object_w29 := (let h_319 : Litex.IsFiniteSet _value_i1 := h_65;
  let h_322 : Litex.In _value_i7 (Litex.Z (M := M)) := h_71;
  let h_332 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_334 : Litex.In _value_i15 (Litex.Z (M := M))) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_335 : Litex.In _value_i16 (Litex.Z (M := M))), Litex.Same (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _value_i15 _value_i16 h_70 h_334 h_335 True.intro) (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _value_i16 _value_i15 h_70 h_335 h_334 True.intro) := (by
    intro _Host_i15 _rep_i15 _value_i15 h_334 _Host_i16 _rep_i16 _value_i16 h_335
    exact (h_6 _value_i15 h_334 _value_i16 h_335)
  );
  let h_361 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_363 : Litex.In _value_i15 (Litex.Z (M := M))) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_364 : Litex.In _value_i16 (Litex.Z (M := M))) {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_365 : Litex.In _value_i17 (Litex.Z (M := M))), Litex.Same (let _object_w27 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _value_i15 _value_i16 h_70 h_363 h_364 True.intro);
  let _wd_1_1 := _value_i17;
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _object_w27 _wd_1_1 h_70 (by
    let _atomic_wd_1_0 := _object_w27
    exact (by
      let _litex_return_call := _object_w27
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_365 True.intro)) (let _wd_1_0 := _value_i15;
  let _object_w28 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _value_i16 _value_i17 h_70 h_364 h_365 True.intro);
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _wd_1_0 _object_w28 h_70 h_363 (by
    let _atomic_wd_1_0 := _object_w28
    exact (by
      let _litex_return_call := _object_w28
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro)) := (by
    intro _Host_i15 _rep_i15 _value_i15 h_363 _Host_i16 _rep_i16 _value_i16 h_364 _Host_i17 _rep_i17 _value_i17 h_365
    exact (h_8 _value_i15 h_363 _value_i16 h_364 _value_i17 h_365)
  );
  let h_576 : Litex.Subset _value_i1 (Litex.Z (M := M)) := h_2;
  let h_582 : ∀ {_Host_i18 : Type _} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_584 : Litex.In _value_i18 _value_i1), ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)) := (by
    intro _Host_i18 _rep_i18 _value_i18 h_584
    exact (h_4 _value_i18 h_584)
  );
  let _fold_guard : ∀ i, M.mem i (Litex.denote _value_i1) → (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) i := Litex.forallMembersOfRepresentations.{u, _, 0} _value_i1 (fun _fold_index _fold_member => h_582 _fold_index _fold_member);
  Litex.finiteFold _value_i1 _value_i2 _value_i4 _value_i7 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) h_319 (Litex.inOfSame _value_i2 _value_i2 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.sameRefl _value_i2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))) h_67) (Litex.inOfSame _value_i4 _value_i4 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True))) (Litex.sameRefl _value_i4) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True)))) h_70) h_322 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) i).mpr ⟨h_576 i hi, _fold_guard i hi⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (h_332 _fold_x0 _fold_h0 _fold_x1 _fold_h1))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (h_361 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))
  exact (by
    let _atomic_wd_1_0 := _object_w29
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_65 _Host_i2 _rep_i2 _value_i2 h_67 _Host_i4 _rep_i4 _value_i4 h_70 _Host_i7 _rep_i7 _value_i7 h_71 h_2 h_4 h_6 h_8
          let _object_w29 := (let h_319 : Litex.IsFiniteSet _value_i1 := h_65;
          let h_322 : Litex.In _value_i7 (Litex.Z (M := M)) := h_71;
          let h_332 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_334 : Litex.In _value_i15 (Litex.Z (M := M))) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_335 : Litex.In _value_i16 (Litex.Z (M := M))), Litex.Same (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _value_i15 _value_i16 h_70 h_334 h_335 True.intro) (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _value_i16 _value_i15 h_70 h_335 h_334 True.intro) := (by
            intro _Host_i15 _rep_i15 _value_i15 h_334 _Host_i16 _rep_i16 _value_i16 h_335
            exact (h_6 _value_i15 h_334 _value_i16 h_335)
          );
          let h_361 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_363 : Litex.In _value_i15 (Litex.Z (M := M))) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_364 : Litex.In _value_i16 (Litex.Z (M := M))) {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_365 : Litex.In _value_i17 (Litex.Z (M := M))), Litex.Same (let _object_w27 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _value_i15 _value_i16 h_70 h_363 h_364 True.intro);
          let _wd_1_1 := _value_i17;
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _object_w27 _wd_1_1 h_70 (by
            let _atomic_wd_1_0 := _object_w27
            exact (by
              let _litex_return_call := _object_w27
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) h_365 True.intro)) (let _wd_1_0 := _value_i15;
          let _object_w28 := (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _value_i16 _value_i17 h_70 h_364 h_365 True.intro);
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _value_i4 _wd_1_0 _object_w28 h_70 h_363 (by
            let _atomic_wd_1_0 := _object_w28
            exact (by
              let _litex_return_call := _object_w28
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.call2InOutput _litex_return_call))) True.intro)) := (by
            intro _Host_i15 _rep_i15 _value_i15 h_363 _Host_i16 _rep_i16 _value_i16 h_364 _Host_i17 _rep_i17 _value_i17 h_365
            exact (h_8 _value_i15 h_363 _value_i16 h_364 _value_i17 h_365)
          );
          let h_576 : Litex.Subset _value_i1 (Litex.Z (M := M)) := h_2;
          let h_582 : ∀ {_Host_i18 : Type _} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_584 : Litex.In _value_i18 _value_i1), ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)) := (by
            intro _Host_i18 _rep_i18 _value_i18 h_584
            exact (h_4 _value_i18 h_584)
          );
          let _fold_guard : ∀ i, M.mem i (Litex.denote _value_i1) → (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) i := Litex.forallMembersOfRepresentations.{u, _, 0} _value_i1 (fun _fold_index _fold_member => h_582 _fold_index _fold_member);
          Litex.finiteFold _value_i1 _value_i2 _value_i4 _value_i7 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))) h_319 (Litex.inOfSame _value_i2 _value_i2 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.sameRefl _value_i2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ)))))))) h_67) (Litex.inOfSame _value_i4 _value_i4 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True))) (Litex.sameRefl _value_i4) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True)))) h_70) h_322 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (0 : ℂ))))) i).mpr ⟨h_576 i hi, _fold_guard i hi⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (h_332 _fold_x0 _fold_h0 _fold_x1 _fold_h1))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Z (M := M)) (fun _fold_x2 _fold_h2 => (h_361 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))
          have h_9 : (by
            let _atomic_wd_1_0 := _object_w29
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w29
                    exact (by
                      have _selected_operation : Litex.In _value_i4 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True))) := h_70
                      exact Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _atomic_wd_1_0) (Litex.sameRefl (Litex.Z (M := M))) (Litex.finiteFoldInOutput _atomic_wd_1_0)))
                )
            )
          exact h_9
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_fold_x5f_guarded_x2f_statement_x2e_lit
