import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_fold_x5f_domains_x2f_statement_x2e_lit

universe u v1 v3 v6 v7 v9 v12 v13 v15 v18
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_77 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.natural) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_75 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_75)
    have h_75 : Litex.In _value_i2 (Litex.N (M := M)) := h_75
    have h_76 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i2 h_75)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_82 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.natural) → M.mem _raw_i5 (M.standard Litex.StandardSetValue.natural) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → True := (by
    intro _raw_i4 _raw_i5 h_78 h_80 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_78)
    have h_78 : Litex.In _value_i4 (Litex.N (M := M)) := h_78
    have h_79 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i4 h_78)
          )
      )
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_80)
    have h_80 : Litex.In _value_i5 (Litex.N (M := M)) := h_80
    have h_81 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i5 h_80)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_83 : Litex.In _value_i6 (Litex.N (M := M))), (by
  let _object_w33 := (let h_85 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
  let h_92 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
  let h_99 : Litex.In _value_i6 (Litex.N (M := M)) := h_83;
  let h_110 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.N (M := M)) := (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num));
  Litex.rangeFold (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) _value_i1 _value_i3 _value_i6 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True)) h_85 h_92 (Litex.inOfSame _value_i1 _value_i1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl _value_i1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True)))) h_77) (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) h_82) h_99 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.natural) (Litex.denote (Litex.N (M := M))) (M.standard_isSet Litex.StandardSetValue.natural) (Litex.isSet (Litex.N (M := M))) (fun (_raw_i2 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInNaturalAbove (Litex.number (M := M) (1 : ℂ)) h_110 k hlow, True.intro⟩))
  exact (by
    let _atomic_wd_1_0 := _object_w33
    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_77 _Host_i3 _rep_i3 _value_i3 h_82 _Host_i6 _rep_i6 _value_i6 h_83
          have h_84 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i6 h_83)
                )
            )
          let _object_w33 := (let h_85 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
          let h_92 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
          let h_99 : Litex.In _value_i6 (Litex.N (M := M)) := h_83;
          let h_110 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.N (M := M)) := (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num));
          Litex.rangeFold (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) _value_i1 _value_i3 _value_i6 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True)) h_85 h_92 (Litex.inOfSame _value_i1 _value_i1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True))) (Litex.sameRefl _value_i1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True)))) h_77) (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) h_82) h_99 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.natural) (Litex.denote (Litex.N (M := M))) (M.standard_isSet Litex.StandardSetValue.natural) (Litex.isSet (Litex.N (M := M))) (fun (_raw_i2 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInNaturalAbove (Litex.number (M := M) (1 : ℂ)) h_110 k hlow, True.intro⟩))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w33
            exact Litex.In _atomic_wd_1_0 (Litex.N (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w33
                    exact (by
                      have _selected_operation : Litex.In _value_i3 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) := h_82
                      exact Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.N (M := M)) (Litex.N (M := M)) (Litex.sameRefl _atomic_wd_1_0) (Litex.sameRefl (Litex.N (M := M))) (Litex.rangeFoldInOutput _atomic_wd_1_0)))
                )
            )
          have h_145 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w33 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _object_w33 h_1)
                )
            )
          exact h_1
        )
      )
  )

theorem h_147 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_223 : Litex.In _value_i7 (let _checked_header : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (M.standard Litex.StandardSetValue.natural) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → True := (by
    intro _raw_i8 h_221 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_221)
    have h_221 : Litex.In _value_i8 (Litex.N (M := M)) := h_221
    have h_222 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i8 h_221)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i8 : M.Value) => True)))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_228 : Litex.In _value_i9 (let _checked_header : ∀ (_raw_i10 : M.Value) (_raw_i11 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.natural) → M.mem _raw_i11 (M.standard Litex.StandardSetValue.natural) → ((fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) _raw_i10 _raw_i11) → True := (by
    intro _raw_i10 _raw_i11 h_224 h_226 _
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_224)
    have h_224 : Litex.In _value_i10 (Litex.N (M := M)) := h_224
    have h_225 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i10 h_224)
          )
      )
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_226)
    have h_226 : Litex.In _value_i11 (Litex.N (M := M)) := h_226
    have h_227 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i11 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i11 h_226)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True)))) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_229 : Litex.In _value_i12 (Litex.N (M := M))), (by
  let _object_w66 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
  let _wd_1_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
  let _wd_1_2 := _value_i7;
  let _wd_1_3 := _value_i9;
  let _wd_1_4 := _value_i12;
  (let h_245 : (by
    let _atomic_wd_1_0 := _wd_1_0
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) := (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num))));
  let h_259 : (by
    let _atomic_wd_1_0 := _wd_1_1
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) := (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num))));
  let h_273 : Litex.In _wd_1_4 (Litex.N (M := M)) := h_229;
  let h_282 : (by
    let _equal_wd_1_0 := _wd_1_0
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-1 : ℂ))) := ((M.neg_numbers (1 : ℂ)).trans (congrArg M.number (by norm_num : -(1 : ℂ) = (-1 : ℂ))));
  let h_283 : (by
    let _equal_wd_1_0 := _wd_1_1
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-2 : ℂ))) := ((M.neg_numbers (2 : ℂ)).trans (congrArg M.number (by norm_num : -(2 : ℂ) = (-2 : ℂ))));
  Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i8 : M.Value) => True)) h_245 h_259 (Litex.inOfSame _wd_1_2 _wd_1_2 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i8 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i8 : M.Value) => True))) (Litex.sameRefl _wd_1_2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i8 : M.Value) => True)))) h_223) (Litex.inOfSame _wd_1_3 _wd_1_3 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True))) (Litex.sameRefl _wd_1_3) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True)))) h_228) h_273 (fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty _wd_1_0 _wd_1_1 (-1 : ℤ) (-2 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_282) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_283) (by decide) k hlow hhigh))))
  exact (by
    let _equal_wd_1_0 := _object_w66
    exact Litex.Same _equal_wd_1_0 _value_i12)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_223 _Host_i9 _rep_i9 _value_i9 h_228 _Host_i12 _rep_i12 _value_i12 h_229
          have h_230 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i12 h_229)
                )
            )
          let _object_w66 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          let _wd_1_2 := _value_i7;
          let _wd_1_3 := _value_i9;
          let _wd_1_4 := _value_i12;
          (let h_245 : (by
            let _atomic_wd_1_0 := _wd_1_0
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) := (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num))));
          let h_259 : (by
            let _atomic_wd_1_0 := _wd_1_1
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) := (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num))));
          let h_273 : Litex.In _wd_1_4 (Litex.N (M := M)) := h_229;
          let h_282 : (by
            let _equal_wd_1_0 := _wd_1_0
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-1 : ℂ))) := ((M.neg_numbers (1 : ℂ)).trans (congrArg M.number (by norm_num : -(1 : ℂ) = (-1 : ℂ))));
          let h_283 : (by
            let _equal_wd_1_0 := _wd_1_1
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-2 : ℂ))) := ((M.neg_numbers (2 : ℂ)).trans (congrArg M.number (by norm_num : -(2 : ℂ) = (-2 : ℂ))));
          Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i8 : M.Value) => True)) h_245 h_259 (Litex.inOfSame _wd_1_2 _wd_1_2 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i8 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i8 : M.Value) => True))) (Litex.sameRefl _wd_1_2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i8 : M.Value) => True)))) h_223) (Litex.inOfSame _wd_1_3 _wd_1_3 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True))) (Litex.sameRefl _wd_1_3) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True)))) h_228) h_273 (fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty _wd_1_0 _wd_1_1 (-1 : ℤ) (-2 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_282) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_283) (by decide) k hlow hhigh))))
          have h_146 : (by
            let _equal_wd_1_0 := _object_w66
            exact Litex.Same _equal_wd_1_0 _value_i12) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w66;
                  (show Litex.Same _equal_wd_1_0 _value_i12 from ((Litex.rangeFoldEmptyOfLt _equal_wd_1_0 (by
                    let _atomic_wd_1_0 := (_equal_wd_1_0).val.last
                    let _atomic_wd_1_1 := (_equal_wd_1_0).val.first
                    exact ((Litex.NativeBridge.lt_iff_asReal _atomic_wd_1_0 _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) = (-2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) = (-1 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
                      let _atomic_wd_2_0 := _atomic_wd_1_1
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))))
                )
            )
          exact h_146
        )
      )
  )

theorem h_397 : ∀ {_Host_i13 : Type v13} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_453 : Litex.In _value_i13 (let _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i14 : M.Value) => (¬ (_raw_i14 = (M.number (0 : ℂ))))) _raw_i14) → True := (by
    intro _raw_i14 h_452 h_395
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_452)
    have h_452 : Litex.In _value_i14 (Litex.Z (M := M)) := h_452
    have h_395 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i14 = (M.number (0 : ℂ))))
              exact h_395)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i14 : M.Value) => (¬ (_raw_i14 = (M.number (0 : ℂ)))))))) {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_456 : Litex.In _value_i15 (let _checked_header : ∀ (_raw_i16 : M.Value) (_raw_i17 : M.Value), M.mem _raw_i16 (M.standard Litex.StandardSetValue.integer) → M.mem _raw_i17 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True) _raw_i16 _raw_i17) → True := (by
    intro _raw_i16 _raw_i17 h_454 h_455 _
    let _value_i16 := Litex.semanticObject (M := M) _raw_i16 (M.member_isSet h_454)
    have h_454 : Litex.In _value_i16 (Litex.Z (M := M)) := h_454
    let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_455)
    have h_455 : Litex.In _value_i17 (Litex.Z (M := M)) := h_455
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True)))) {_Host_i18 : Type v18} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_457 : Litex.In _value_i18 (Litex.Z (M := M))), (by
  let _object_w91 := (let h_458 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
  let h_465 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
  let h_472 : Litex.In _value_i18 (Litex.Z (M := M)) := h_457;
  let h_481 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _);
  let h_482 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _);
  let h_485 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _);
  let h_486 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _);
  Litex.rangeFold (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _value_i13 _value_i15 _value_i18 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i14 : M.Value) => (¬ (_raw_i14 = (M.number (0 : ℂ)))))) h_458 h_465 (Litex.inOfSame _value_i13 _value_i13 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i14 : M.Value) => (¬ (_raw_i14 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i14 : M.Value) => (¬ (_raw_i14 = (M.number (0 : ℂ))))))) (Litex.sameRefl _value_i13) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i14 : M.Value) => (¬ (_raw_i14 = (M.number (0 : ℂ)))))))) h_453) (Litex.inOfSame _value_i15 _value_i15 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True))) (Litex.sameRefl _value_i15) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True)))) h_456) h_472 (fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℤ) (0 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_481) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_482) (by decide) k hlow hhigh)))
  exact (by
    let _equal_wd_1_0 := _object_w91
    exact Litex.Same _equal_wd_1_0 _value_i18)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i13 _rep_i13 _value_i13 h_453 _Host_i15 _rep_i15 _value_i15 h_456 _Host_i18 _rep_i18 _value_i18 h_457
          let _object_w91 := (let h_458 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
          let h_465 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
          let h_472 : Litex.In _value_i18 (Litex.Z (M := M)) := h_457;
          let h_481 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _);
          let h_482 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _);
          let h_485 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _);
          let h_486 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _);
          Litex.rangeFold (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) _value_i13 _value_i15 _value_i18 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i14 : M.Value) => (¬ (_raw_i14 = (M.number (0 : ℂ)))))) h_458 h_465 (Litex.inOfSame _value_i13 _value_i13 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i14 : M.Value) => (¬ (_raw_i14 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i14 : M.Value) => (¬ (_raw_i14 = (M.number (0 : ℂ))))))) (Litex.sameRefl _value_i13) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i14 : M.Value) => (¬ (_raw_i14 = (M.number (0 : ℂ)))))))) h_453) (Litex.inOfSame _value_i15 _value_i15 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True))) (Litex.sameRefl _value_i15) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i16 : M.Value) (_raw_i17 : M.Value) => True)))) h_456) h_472 (fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℤ) (0 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_481) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_482) (by decide) k hlow hhigh)))
          have h_396 : (by
            let _equal_wd_1_0 := _object_w91
            exact Litex.Same _equal_wd_1_0 _value_i18) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w91;
                  (show Litex.Same _equal_wd_1_0 _value_i18 from ((Litex.rangeFoldEmptyOfLt _equal_wd_1_0 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))))
                )
            )
          exact h_396
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_fold_x5f_domains_x2f_statement_x2e_lit
