import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_division_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.C (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_19 : Litex.In _value_i3 (Litex.C (M := M))) (h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) (h_2 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w3 := (let _wd_1_0 := (Litex.div _value_i1 _value_i2 h_17 h_18 h_1);
  let _wd_1_1 := _value_i3;
  (Litex.div _wd_1_0 _wd_1_1 (Litex.divInC _value_i1 _value_i2 h_17 h_18 (_wd_1_0).wd.2.2) h_19 h_2))
  let _object_w4 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.mul _value_i2 _value_i3 h_18 h_19);
  (Litex.div _wd_1_0 _wd_1_1 h_17 (Litex.mulInC _value_i2 _value_i3 h_18 h_19) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) ((Litex.NativeBridge.asComplex _value_i2 h_18) * (Litex.NativeBridge.asComplex _value_i3 h_19)) (0 : ℂ) (Litex.NativeBridge.denoteMul _value_i2 _value_i3 h_18 h_19 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 h_18) (Litex.NativeBridge.asComplex_spec _value_i3 h_19)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (mul_ne_zero (Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 h_18) (Litex.NativeBridge.asComplex_spec _value_i2 h_18) h_1) (Litex.NativeBridge.nativeNonzeroOfDenote _value_i3 (Litex.NativeBridge.asComplex _value_i3 h_19) (Litex.NativeBridge.asComplex_spec _value_i3 h_19) h_2)))))
  exact Litex.Same _object_w3 _object_w4
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 _Host_i3 _rep_i3 _value_i3 h_19 h_1 h_2
    let _object_w3 := (let _wd_1_0 := (Litex.div _value_i1 _value_i2 h_17 h_18 h_1);
    let _wd_1_1 := _value_i3;
    (Litex.div _wd_1_0 _wd_1_1 (Litex.divInC _value_i1 _value_i2 h_17 h_18 (_wd_1_0).wd.2.2) h_19 h_2))
    let _object_w4 := (let _wd_1_0 := _value_i1;
    let _wd_1_1 := (Litex.mul _value_i2 _value_i3 h_18 h_19);
    (Litex.div _wd_1_0 _wd_1_1 h_17 (Litex.mulInC _value_i2 _value_i3 h_18 h_19) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) ((Litex.NativeBridge.asComplex _value_i2 h_18) * (Litex.NativeBridge.asComplex _value_i3 h_19)) (0 : ℂ) (Litex.NativeBridge.denoteMul _value_i2 _value_i3 h_18 h_19 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 h_18) (Litex.NativeBridge.asComplex_spec _value_i3 h_19)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (mul_ne_zero (Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 h_18) (Litex.NativeBridge.asComplex_spec _value_i2 h_18) h_1) (Litex.NativeBridge.nativeNonzeroOfDenote _value_i3 (Litex.NativeBridge.asComplex _value_i3 h_19) (Litex.NativeBridge.asComplex_spec _value_i3 h_19) h_2)))))
    have h_3 : Litex.Same _object_w3 _object_w4 :=
      (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 h_17) / (Litex.NativeBridge.asComplex _value_i2 h_18)) / (Litex.NativeBridge.asComplex _value_i3 h_19)) ((Litex.NativeBridge.asComplex _value_i1 h_17) / ((Litex.NativeBridge.asComplex _value_i2 h_18) * (Litex.NativeBridge.asComplex _value_i3 h_19))) (Litex.NativeBridge.denoteDiv (_object_w3).val.left _value_i3 (_object_w3).wd.1 (_object_w3).wd.2.1 (_object_w3).wd.2.2 _ _ (Litex.NativeBridge.denoteDiv _value_i1 _value_i2 ((_object_w3).val.left).wd.1 ((_object_w3).val.left).wd.2.1 ((_object_w3).val.left).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_17) (Litex.NativeBridge.asComplex_spec _value_i2 h_18)) (Litex.NativeBridge.asComplex_spec _value_i3 h_19)) (Litex.NativeBridge.denoteDiv _value_i1 (_object_w4).val.right (_object_w4).wd.1 (_object_w4).wd.2.1 (_object_w4).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_17) (Litex.NativeBridge.denoteMul _value_i2 _value_i3 ((_object_w4).val.right).wd.1 ((_object_w4).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 h_18) (Litex.NativeBridge.asComplex_spec _value_i3 h_19))) (by
        have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i2 h_18) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 h_18) (Litex.NativeBridge.asComplex_spec _value_i2 h_18) h_1
        have _litex_nz_1 : ((Litex.NativeBridge.asComplex _value_i3 h_19) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i3 (Litex.NativeBridge.asComplex _value_i3 h_19) (Litex.NativeBridge.asComplex_spec _value_i3 h_19) h_2
        litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | exact _litex_nz_1 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
      ))
    exact h_3
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_division_x2f_statement_x2e_lit
