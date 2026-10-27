import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_fold_x5f_guarded_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v8 v9
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_7 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_74 : Litex.In _value_i1 (Litex.Z (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_75 : Litex.In _value_i2 (Litex.Z (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_77 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
    intro _raw_i4 h_76 h_1
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_76)
    have h_76 : Litex.In _value_i4 (Litex.Z (M := M)) := h_76
    have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i4 = (M.number (0 : ℂ))))
              exact h_1)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_80 : Litex.In _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value) (_raw_i7 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.integer) → M.mem _raw_i7 (M.standard Litex.StandardSetValue.integer) → ((fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True) _raw_i6 _raw_i7) → True := (by
    intro _raw_i6 _raw_i7 h_78 h_79 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_78)
    have h_78 : Litex.In _value_i6 (Litex.Z (M := M)) := h_78
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_79)
    have h_79 : Litex.In _value_i7 (Litex.Z (M := M)) := h_79
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True)))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_81 : Litex.In _value_i8 (Litex.Z (M := M))) (h_5 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_82 : Litex.In _value_i9 (Litex.Z (M := M))) (h_2 : Litex.Le _value_i1 _value_i9) (h_3 : Litex.Le _value_i9 _value_i2), ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w23 := (let h_416 : Litex.In _value_i1 (Litex.Z (M := M)) := h_74;
  let h_421 : Litex.In _value_i2 (Litex.Z (M := M)) := h_75;
  let h_428 : Litex.In _value_i8 (Litex.Z (M := M)) := h_81;
  let h_444 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_448 : Litex.In _value_i10 (Litex.Z (M := M))) (h_441 : Litex.Le _value_i1 _value_i10) (h_442 : Litex.Le _value_i10 _value_i2), ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) := (by
    intro _Host_i10 _rep_i10 _value_i10 h_448 h_441 h_442
    exact (h_5 _value_i10 h_448 h_441 h_442)
  );
  Litex.rangeFold _value_i1 _value_i2 _value_i3 _value_i5 _value_i8 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))) h_416 h_421 (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))) h_77) (Litex.inOfSame _value_i5 _value_i5 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True))) (Litex.sameRefl _value_i5) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True)))) h_80) h_428 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, h_444 (Litex.number (M := M) (k : ℂ)) (Litex.NativeBridge.numberInZ k) (Litex.integerLowerBound _value_i1 h_416 k hlow) (Litex.integerUpperBound _value_i2 h_421 k hhigh)⟩))
  exact (by
    let _atomic_wd_1_0 := _object_w23
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_74 _Host_i2 _rep_i2 _value_i2 h_75 _Host_i3 _rep_i3 _value_i3 h_77 _Host_i5 _rep_i5 _value_i5 h_80 _Host_i8 _rep_i8 _value_i8 h_81 h_5
          let _object_w23 := (let h_416 : Litex.In _value_i1 (Litex.Z (M := M)) := h_74;
          let h_421 : Litex.In _value_i2 (Litex.Z (M := M)) := h_75;
          let h_428 : Litex.In _value_i8 (Litex.Z (M := M)) := h_81;
          let h_444 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_448 : Litex.In _value_i10 (Litex.Z (M := M))) (h_441 : Litex.Le _value_i1 _value_i10) (h_442 : Litex.Le _value_i10 _value_i2), ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) := (by
            intro _Host_i10 _rep_i10 _value_i10 h_448 h_441 h_442
            exact (h_5 _value_i10 h_448 h_441 h_442)
          );
          Litex.rangeFold _value_i1 _value_i2 _value_i3 _value_i5 _value_i8 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))) h_416 h_421 (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ)))))))) h_77) (Litex.inOfSame _value_i5 _value_i5 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True))) (Litex.sameRefl _value_i5) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True)))) h_80) h_428 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, h_444 (Litex.number (M := M) (k : ℂ)) (Litex.NativeBridge.numberInZ k) (Litex.integerLowerBound _value_i1 h_416 k hlow) (Litex.integerUpperBound _value_i2 h_421 k hhigh)⟩))
          have h_6 : (by
            let _atomic_wd_1_0 := _object_w23
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w23
                    exact (by
                      have _selected_operation : Litex.In _value_i5 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => True))) := h_80
                      exact Litex.inOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _atomic_wd_1_0) (Litex.sameRefl (Litex.Z (M := M))) (Litex.rangeFoldInOutput _atomic_wd_1_0)))
                )
            )
          exact h_6
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_fold_x5f_guarded_x2f_statement_x2e_lit
