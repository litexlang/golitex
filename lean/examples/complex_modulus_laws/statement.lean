import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_modulus_x5f_laws_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.C (M := M))), (by
  let _object_w2 := (Litex.complexAbs _value_i1 h_15)
  exact (by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15
          let _object_w2 := (Litex.complexAbs _value_i1 h_15)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.NativeBridge.leOfDenoteReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0 0 ‖((Litex.NativeBridge.asComplex _value_i1 h_15))‖ (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))) (Litex.denoteComplexAbs _atomic_wd_1_0 (Litex.NativeBridge.asComplex _value_i1 h_15) (Litex.NativeBridge.asComplex_spec _value_i1 h_15)) (norm_nonneg _)))
                )
            )
          exact h_1
        )
      )
  )

theorem h_53 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_78 : Litex.In _value_i2 (Litex.C (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_79 : Litex.In _value_i3 (Litex.C (M := M))), (by
  let _object_w5 := (let _wd_1_0 := (Litex.mul _value_i2 _value_i3 h_78 h_79);
  (Litex.complexAbs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC _value_i2 _value_i3 h_78 h_79))))
  let _object_w6 := (let _wd_1_0 := (Litex.complexAbs _value_i2 h_78);
  let _wd_1_1 := (Litex.complexAbs _value_i3 h_79);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.complexAbs _value_i2 h_78)
    exact (M.real_subset_complex _ (Litex.complexAbsInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.complexAbs _value_i3 h_79)
    exact (M.real_subset_complex _ (Litex.complexAbsInR _atomic_wd_1_0)))))
  exact (by
    let _equal_wd_1_0 := _object_w5
    let _equal_wd_1_1 := _object_w6
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_78 _Host_i3 _rep_i3 _value_i3 h_79
          let _object_w5 := (let _wd_1_0 := (Litex.mul _value_i2 _value_i3 h_78 h_79);
          (Litex.complexAbs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInC _value_i2 _value_i3 h_78 h_79))))
          let _object_w6 := (let _wd_1_0 := (Litex.complexAbs _value_i2 h_78);
          let _wd_1_1 := (Litex.complexAbs _value_i3 h_79);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.complexAbs _value_i2 h_78)
            exact (M.real_subset_complex _ (Litex.complexAbsInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.complexAbs _value_i3 h_79)
            exact (M.real_subset_complex _ (Litex.complexAbsInR _atomic_wd_1_0)))))
          have h_52 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w5;
                  let _equal_wd_1_1 := _object_w6;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (‖(((Litex.NativeBridge.asComplex _value_i2 h_78) * (Litex.NativeBridge.asComplex _value_i3 h_79)))‖ : ℂ) ((‖((Litex.NativeBridge.asComplex _value_i2 h_78))‖ : ℂ) * (‖((Litex.NativeBridge.asComplex _value_i3 h_79))‖ : ℂ)) (let _complex := _equal_wd_1_0; Litex.denoteComplexAbs _complex ((Litex.NativeBridge.asComplex _value_i2 h_78) * (Litex.NativeBridge.asComplex _value_i3 h_79)) (Litex.NativeBridge.denoteMul _value_i2 _value_i3 ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 h_78) (Litex.NativeBridge.asComplex_spec _value_i3 h_79))) (Litex.NativeBridge.denoteMul (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (let _complex := (_equal_wd_1_1).val.left; Litex.denoteComplexAbs _complex (Litex.NativeBridge.asComplex _value_i2 h_78) (Litex.NativeBridge.asComplex_spec _value_i2 h_78)) (let _complex := (_equal_wd_1_1).val.right; Litex.denoteComplexAbs _complex (Litex.NativeBridge.asComplex _value_i3 h_79) (Litex.NativeBridge.asComplex_spec _value_i3 h_79))) (by simp only [norm_mul, Complex.ofReal_mul]))))
                )
            )
          exact h_52
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_modulus_x5f_laws_x2f_statement_x2e_lit
