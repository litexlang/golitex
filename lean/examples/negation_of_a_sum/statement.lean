import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_negation_x5f_of_x5f_a_x5f_sum_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem fact_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (_h_param_i1 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (_h_param_i2 : Litex.In _value_i2 (Litex.C (M := M))), Litex.Same (Litex.neg (Litex.add _value_i1 _value_i2 _h_param_i1 _h_param_i2) (Litex.addInC _value_i1 _value_i2 _h_param_i1 _h_param_i2)) (Litex.sub (Litex.neg _value_i1 _h_param_i1) _value_i2 (Litex.negInC _value_i1 _h_param_i1) _h_param_i2) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 _h_param_i1 _Host_i2 _rep_i2 _value_i2 _h_param_i2
    exact (Litex.NativeBridge.sameOfDenoteNumber (Litex.neg (Litex.add _value_i1 _value_i2 _h_param_i1 _h_param_i2) (Litex.addInC _value_i1 _value_i2 _h_param_i1 _h_param_i2)) (Litex.sub (Litex.neg _value_i1 _h_param_i1) _value_i2 (Litex.negInC _value_i1 _h_param_i1) _h_param_i2) (- ((Litex.NativeBridge.asComplex _value_i1 _h_param_i1) + (Litex.NativeBridge.asComplex _value_i2 _h_param_i2))) ((- (Litex.NativeBridge.asComplex _value_i1 _h_param_i1)) - (Litex.NativeBridge.asComplex _value_i2 _h_param_i2)) (Litex.NativeBridge.denoteNeg (Litex.add _value_i1 _value_i2 _h_param_i1 _h_param_i2) (Litex.addInC _value_i1 _value_i2 _h_param_i1 _h_param_i2) ((Litex.NativeBridge.asComplex _value_i1 _h_param_i1) + (Litex.NativeBridge.asComplex _value_i2 _h_param_i2)) (Litex.NativeBridge.denoteAdd _value_i1 _value_i2 _h_param_i1 _h_param_i2 (Litex.NativeBridge.asComplex _value_i1 _h_param_i1) (Litex.NativeBridge.asComplex _value_i2 _h_param_i2) (Litex.NativeBridge.asComplex_spec _value_i1 _h_param_i1) (Litex.NativeBridge.asComplex_spec _value_i2 _h_param_i2))) (Litex.NativeBridge.denoteSub (Litex.neg _value_i1 _h_param_i1) _value_i2 (Litex.negInC _value_i1 _h_param_i1) _h_param_i2 (- (Litex.NativeBridge.asComplex _value_i1 _h_param_i1)) (Litex.NativeBridge.asComplex _value_i2 _h_param_i2) (Litex.NativeBridge.denoteNeg _value_i1 _h_param_i1 (Litex.NativeBridge.asComplex _value_i1 _h_param_i1) (Litex.NativeBridge.asComplex_spec _value_i1 _h_param_i1)) (Litex.NativeBridge.asComplex_spec _value_i2 _h_param_i2)) (by ring))
  )
end LitexCompiled.file_lean_x2f_examples_x2f_negation_x5f_of_x5f_a_x5f_sum_x2f_statement_x2e_lit
