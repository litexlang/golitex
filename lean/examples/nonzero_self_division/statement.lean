import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_self_x5f_division_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.C (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w3 := (Litex.div _value_i1 _value_i1 h_16 h_16 h_1)
  exact Litex.Same _object_w3 (Litex.number (M := M) (1 : ℂ))
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
    let _object_w3 := (Litex.div _value_i1 _value_i1 h_16 h_16 h_1)
    have h_2 : Litex.Same _object_w3 (Litex.number (M := M) (1 : ℂ)) :=
      (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 h_16) / (Litex.NativeBridge.asComplex _value_i1 h_16)) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i1 _value_i1 (_object_w3).wd.1 (_object_w3).wd.2.1 (_object_w3).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_16) (Litex.NativeBridge.asComplex_spec _value_i1 h_16)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
        have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i1 h_16) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i1 (Litex.NativeBridge.asComplex _value_i1 h_16) (Litex.NativeBridge.asComplex_spec _value_i1 h_16) h_1
        litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
      ))
    exact h_2
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_self_x5f_division_x2f_statement_x2e_lit
