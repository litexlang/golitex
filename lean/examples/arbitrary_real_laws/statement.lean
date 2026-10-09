import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_arbitrary_x5f_real_x5f_laws_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_1 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M)))

theorem h_3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : Litex.Same _value_i1 _value_i1 :=
  (Litex.sameRefl _value_i1)

theorem h_5 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : Litex.Same (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_2) (Litex.numberInC (M := M) (0 : ℂ))) _value_i1 :=
  (Litex.NativeBridge.sameOfDenoteNumber (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_2) (Litex.numberInC (M := M) (0 : ℂ))) _value_i1 ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_2)) + (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_2)) (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.realToComplex _value_i1 h_2) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_2)) (0 : ℂ) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_2)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_2)) (by ring))

theorem h_21 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : Litex.Le _value_i1 _value_i1 :=
  (Litex.leRefl _value_i1 h_2)
end LitexCompiled.file_lean_x2f_examples_x2f_arbitrary_x5f_real_x5f_laws_x2f_statement_x2e_lit
