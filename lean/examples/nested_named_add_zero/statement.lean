import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_named_x5f_add_x5f_zero_x2f_statement_x2e_lit

universe u v1 v3
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_3 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Same (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_3) (Litex.numberInC (M := M) (0 : ℂ))) _value_i1 :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_3
    have h_17 : Litex.In _value_i1 (Litex.R (M := M)) :=
      h_3
    exact (Litex.NativeBridge.sameOfDenoteNumber (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_17) (Litex.numberInC (M := M) (0 : ℂ))) _value_i1 ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_17)) + (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_17)) (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_17) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_17)) (0 : ℂ) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_17)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_17)) (by ring))
  )

theorem h_48 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_50 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same (Litex.add _value_i3 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i3 h_50) (Litex.numberInC (M := M) (0 : ℂ))) _value_i3 :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 h_50
    have h_64 : Litex.In _value_i3 (Litex.R (M := M)) :=
      h_50
    have h_49 : (let h_65 : Litex.In _value_i3 (Litex.R (M := M)) :=
      h_64;
    Litex.Same (Litex.add _value_i3 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i3 h_65) (Litex.numberInC (M := M) (0 : ℂ))) _value_i3) :=
      (by
        have h_65 : Litex.In _value_i3 (Litex.R (M := M)) :=
          h_64
        have h_66 : Litex.Same (Litex.add _value_i3 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i3 h_65) (Litex.numberInC (M := M) (0 : ℂ))) _value_i3 :=
          ((h_2 (M := M)) _value_i3 h_65)
        exact (((Litex.sameRefl (Litex.add _value_i3 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i3 h_65) (Litex.numberInC (M := M) (0 : ℂ))))).symm.trans ((h_66).trans (Litex.sameRefl _value_i3)))
      )
    exact (((Litex.sameRefl (Litex.add _value_i3 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i3 h_64) (Litex.numberInC (M := M) (0 : ℂ))))).trans h_49)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_named_x5f_add_x5f_zero_x2f_statement_x2e_lit
