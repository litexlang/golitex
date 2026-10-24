import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_negation_x5f_of_x5f_a_x5f_sum_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_16 : Litex.In _value_i2 (Litex.C (M := M))), (by
  let _object_w2 := (let _wd_1_0 := (Litex.add _value_i1 _value_i2 h_15 h_16);
  (Litex.neg _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC _value_i1 _value_i2 h_15 h_16))))
  let _object_w3 := (let _wd_1_0 := (Litex.neg _value_i1 h_15);
  let _wd_1_1 := _value_i2;
  (Litex.sub _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.negInC _value_i1 h_15)) h_16))
  exact (by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w3
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15 _Host_i2 _rep_i2 _value_i2 h_16
          let _object_w2 := (let _wd_1_0 := (Litex.add _value_i1 _value_i2 h_15 h_16);
          (Litex.neg _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i1 _value_i2 h_15 h_16))))
          let _object_w3 := (let _wd_1_0 := (Litex.neg _value_i1 h_15);
          let _wd_1_1 := _value_i2;
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.negInC _value_i1 h_15)) h_16))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            let _equal_wd_1_1 := _object_w3
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  let _equal_wd_1_1 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (- ((Litex.NativeBridge.asComplex _value_i1 h_15) + (Litex.NativeBridge.asComplex _value_i2 h_16))) ((- (Litex.NativeBridge.asComplex _value_i1 h_15)) - (Litex.NativeBridge.asComplex _value_i2 h_16)) (Litex.NativeBridge.denoteNeg (_equal_wd_1_0).val.arg (_equal_wd_1_0).wd _ (Litex.NativeBridge.denoteAdd _value_i1 _value_i2 ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_15) (Litex.NativeBridge.asComplex_spec _value_i2 h_16))) (Litex.NativeBridge.denoteSub (_equal_wd_1_1).val.left _value_i2 (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNeg _value_i1 ((_equal_wd_1_1).val.left).wd _ (Litex.NativeBridge.asComplex_spec _value_i1 h_15)) (Litex.NativeBridge.asComplex_spec _value_i2 h_16)) (by ring!))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_negation_x5f_of_x5f_a_x5f_sum_x2f_statement_x2e_lit
