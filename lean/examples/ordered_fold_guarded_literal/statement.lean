import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_fold_x5f_guarded_x5f_literal_x2f_statement_x2e_lit

universe u v1 v3 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_59 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → True := (by
    intro _raw_i2 h_58 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_58)
    have h_58 : Litex.In _value_i2 (Litex.Z (M := M)) := h_58
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
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_62 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value) (_raw_i5 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.integer) → M.mem _raw_i5 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _raw_i4 _raw_i5) → True := (by
    intro _raw_i4 _raw_i5 h_60 h_61 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_60)
    have h_60 : Litex.In _value_i4 (Litex.Z (M := M)) := h_60
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_61)
    have h_61 : Litex.In _value_i5 (Litex.Z (M := M)) := h_61
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_63 : Litex.In _value_i6 (Litex.Z (M := M))), (by
  let _object_w25 := (let h_64 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
  let h_71 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
  let h_78 : Litex.In _value_i6 (Litex.Z (M := M)) := h_63;
  let h_89 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _);
  let h_90 : Litex.Same (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _);
  let h_93 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
  let h_94 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
  let h_95 : ¬ Litex.Same (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
  let _fold_guards : ∀ k ∈ Litex.integerFoldIndices (1 : ℤ) (3 : ℤ), (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (M.number (k : ℂ)) := (by
    intro k hk
    rw [show Litex.integerFoldIndices (1 : ℤ) (3 : ℤ) = [(1 : ℤ), (2 : ℤ), (3 : ℤ)] from by decide] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · have _recorded : (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (M.number (1 : ℂ)) := h_93
      simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using _recorded
    · have _recorded : (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (M.number (2 : ℂ)) := h_94
      simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using _recorded
    · have _recorded : (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (M.number (3 : ℂ)) := h_95
      simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using _recorded
  );
  Litex.rangeFold (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) _value_i1 _value_i3 _value_i6 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) h_64 h_71 (Litex.inOfSame _value_i1 _value_i1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.sameRefl _value_i1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))) h_59) (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) h_62) h_78 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, Litex.integerRangeGuards (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℤ) (3 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_89) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_90) (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _fold_guards k hlow hhigh⟩))
  exact (by
    let _atomic_wd_1_0 := _object_w25
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_59 _Host_i3 _rep_i3 _value_i3 h_62 _Host_i6 _rep_i6 _value_i6 h_63
          let _object_w25 := (let h_64 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
          let h_71 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
          let h_78 : Litex.In _value_i6 (Litex.Z (M := M)) := h_63;
          let h_89 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _);
          let h_90 : Litex.Same (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _);
          let h_93 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
          let h_94 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
          let h_95 : ¬ Litex.Same (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
          let _fold_guards : ∀ k ∈ Litex.integerFoldIndices (1 : ℤ) (3 : ℤ), (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (M.number (k : ℂ)) := (by
            intro k hk
            rw [show Litex.integerFoldIndices (1 : ℤ) (3 : ℤ) = [(1 : ℤ), (2 : ℤ), (3 : ℤ)] from by decide] at hk
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl | rfl
            · have _recorded : (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (M.number (1 : ℂ)) := h_93
              simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using _recorded
            · have _recorded : (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (M.number (2 : ℂ)) := h_94
              simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using _recorded
            · have _recorded : (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (M.number (3 : ℂ)) := h_95
              simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using _recorded
          );
          Litex.rangeFold (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) _value_i1 _value_i3 _value_i6 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) h_64 h_71 (Litex.inOfSame _value_i1 _value_i1 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.sameRefl _value_i1) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))))) h_59) (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True)))) h_62) h_78 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, Litex.integerRangeGuards (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℤ) (3 : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_89) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using h_90) (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _fold_guards k hlow hhigh⟩))
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w25
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w25
                    exact (by
                      have _selected_operation : Litex.In _value_i3 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True))) := h_62
                      exact Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _atomic_wd_1_0) (Litex.sameRefl (Litex.Z (M := M))) (Litex.rangeFoldInOutput _atomic_wd_1_0)))
                )
            )
          exact h_2
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_fold_x5f_guarded_x5f_literal_x2f_statement_x2e_lit
