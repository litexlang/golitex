import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_negation_x5f_of_x5f_a_x5f_sum_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_16 : Litex.In _value_i2 (Litex.C (M := M))), Litex.Same (Litex.neg (Litex.add _value_i1 _value_i2 h_15 h_16) (Litex.addInC _value_i1 _value_i2 h_15 h_16)) (Litex.sub (Litex.neg _value_i1 h_15) _value_i2 (Litex.negInC _value_i1 h_15) h_16) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_15 _Host_i2 _rep_i2 _value_i2 h_16
    have h_1 : Litex.Same (Litex.neg (Litex.add _value_i1 _value_i2 h_15 h_16) (Litex.addInC _value_i1 _value_i2 h_15 h_16)) (Litex.sub (Litex.neg _value_i1 h_15) _value_i2 (Litex.negInC _value_i1 h_15) h_16) :=
      (Litex.NativeBridge.sameOfDenoteNumber (Litex.neg (Litex.add _value_i1 _value_i2 h_15 h_16) (Litex.addInC _value_i1 _value_i2 h_15 h_16)) (Litex.sub (Litex.neg _value_i1 h_15) _value_i2 (Litex.negInC _value_i1 h_15) h_16) (- ((Litex.NativeBridge.asComplex _value_i1 h_15) + (Litex.NativeBridge.asComplex _value_i2 h_16))) ((- (Litex.NativeBridge.asComplex _value_i1 h_15)) - (Litex.NativeBridge.asComplex _value_i2 h_16)) (Litex.NativeBridge.denoteNeg (Litex.add _value_i1 _value_i2 h_15 h_16) (Litex.addInC _value_i1 _value_i2 h_15 h_16) ((Litex.NativeBridge.asComplex _value_i1 h_15) + (Litex.NativeBridge.asComplex _value_i2 h_16)) (Litex.NativeBridge.denoteAdd _value_i1 _value_i2 h_15 h_16 (Litex.NativeBridge.asComplex _value_i1 h_15) (Litex.NativeBridge.asComplex _value_i2 h_16) (Litex.NativeBridge.asComplex_spec _value_i1 h_15) (Litex.NativeBridge.asComplex_spec _value_i2 h_16))) (Litex.NativeBridge.denoteSub (Litex.neg _value_i1 h_15) _value_i2 (Litex.negInC _value_i1 h_15) h_16 (- (Litex.NativeBridge.asComplex _value_i1 h_15)) (Litex.NativeBridge.asComplex _value_i2 h_16) (Litex.NativeBridge.denoteNeg _value_i1 h_15 (Litex.NativeBridge.asComplex _value_i1 h_15) (Litex.NativeBridge.asComplex_spec _value_i1 h_15)) (Litex.NativeBridge.asComplex_spec _value_i2 h_16)) (by ring))
    exact h_1
  )
end LitexCompiled.file_lean_x2f_examples_x2f_negation_x5f_of_x5f_a_x5f_sum_x2f_statement_x2e_lit
