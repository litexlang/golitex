import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_self_x5f_division_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem fact_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (_h_param_i1 : Litex.In _value_i1 (Litex.C (M := M))) (_h_dom_f1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), Litex.Same (Litex.div _value_i1 _value_i1 _h_param_i1 _h_param_i1 _h_dom_f1) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 _h_param_i1 _h_dom_f1
    exact (Litex.NativeBridge.sameOfDenoteNumber (Litex.div _value_i1 _value_i1 _h_param_i1 _h_param_i1 _h_dom_f1) (Litex.number (M := M) (1 : ℂ)) ((Litex.NativeBridge.asComplex _value_i1 _h_param_i1) / (Litex.NativeBridge.asComplex _value_i1 _h_param_i1)) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i1 _value_i1 _h_param_i1 _h_param_i1 _h_dom_f1 (Litex.NativeBridge.asComplex _value_i1 _h_param_i1) (Litex.NativeBridge.asComplex _value_i1 _h_param_i1) (Litex.NativeBridge.asComplex_spec _value_i1 _h_param_i1) (Litex.NativeBridge.asComplex_spec _value_i1 _h_param_i1)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
    have _litex_nz_0 : (Litex.NativeBridge.asComplex _value_i1 _h_param_i1) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i1 (Litex.NativeBridge.asComplex _value_i1 _h_param_i1) (Litex.NativeBridge.asComplex_spec _value_i1 _h_param_i1) _h_dom_f1
    field_simp (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero) only [_litex_nz_0] <;> ring
  ))
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_self_x5f_division_x2f_statement_x2e_lit
