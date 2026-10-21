import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_division_x5f_cancellation_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.In _value_i2 (Litex.C (M := M))) (h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w3 := (let _wd_1_0 := (Litex.div _value_i1 _value_i2 h_16 h_17 h_1);
  let _wd_1_1 := _value_i2;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.div _value_i1 _wd_1_1 h_16 h_17 h_1)
    exact (Litex.divInC _value_i1 _wd_1_1 h_16 h_17 (_atomic_wd_1_0).wd.2.2)) h_17))
  exact Litex.Same _object_w3 _value_i1
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i2 _rep_i2 _value_i2 h_17 h_1
    let _object_w3 := (let _wd_1_0 := (Litex.div _value_i1 _value_i2 h_16 h_17 h_1);
    let _wd_1_1 := _value_i2;
    (Litex.mul _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (Litex.div _value_i1 _wd_1_1 h_16 h_17 h_1)
      exact (Litex.divInC _value_i1 _wd_1_1 h_16 h_17 (_atomic_wd_1_0).wd.2.2)) h_17))
    have h_2 : Litex.Same _object_w3 _value_i1 :=
      (by
        let _quotient := (_object_w3).val.left
        let _product := _object_w3
        have _child : Litex.Same (Litex.div _value_i1 _value_i2 h_16 h_17 h_1) (Litex.div _value_i1 _value_i2 h_16 h_17 h_1) := (show @Eq M.Value _ _ from Eq.refl _)
        have _conversion := Litex.sameDivIffSameMul _quotient.val.left _quotient.val.right _product.val.left _quotient.wd.1 _quotient.wd.2.1 _product.wd.1 _quotient.wd.2.2
        exact ((_conversion.mp _child).symm))
    exact h_2
  )
end LitexCompiled.file_lean_x2f_examples_x2f_division_x5f_cancellation_x2f_statement_x2e_lit
