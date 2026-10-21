import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_rational_x5f_division_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.Q (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.In _value_i2 (Litex.Q (M := M))) (h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w3 := (Litex.div _value_i1 _value_i2 (Litex.rationalToComplex _value_i1 h_16) (Litex.rationalToComplex _value_i2 h_17) h_1)
  exact (by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i2 _rep_i2 _value_i2 h_17 h_1
    let _object_w3 := (Litex.div _value_i1 _value_i2 (Litex.rationalToComplex _value_i1 h_16) (Litex.rationalToComplex _value_i2 h_17) h_1)
    have h_2 : (by
      let _atomic_wd_1_0 := _object_w3
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M))) :=
      (by
        let _atomic_wd_1_0 := _object_w3
        exact (Litex.divInQ _value_i1 _value_i2 h_16 h_17 (_atomic_wd_1_0).wd.2.2))
    exact h_2
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_rational_x5f_division_x2f_statement_x2e_lit
