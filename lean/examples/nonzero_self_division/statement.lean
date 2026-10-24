import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_self_x5f_division_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.C (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w3 := (Litex.div _value_i1 _value_i1 h_16 h_16 h_1)
  exact (by
    let _equal_wd_1_0 := _object_w3
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
          let _object_w3 := (Litex.div _value_i1 _value_i1 h_16 h_16 h_1)
          have h_2 : (by
            let _equal_wd_1_0 := _object_w3
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (by
                    let _quotient := _equal_wd_1_0
                    let _product := (Litex.mul (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) h_16)
                    have _child : (by
                      let _equal_wd_2_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) h_16)
                      exact Litex.Same _value_i1 _equal_wd_2_1) := (let _equal_wd_2_1 := (Litex.mul (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) h_16);
                    (show Litex.Same _value_i1 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (Litex.NativeBridge.asComplex _value_i1 h_16) ((1 : ℂ) * (Litex.NativeBridge.asComplex _value_i1 h_16)) (Litex.NativeBridge.asComplex_spec _value_i1 h_16) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (1 : ℂ)) _value_i1 (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i1 h_16)) (by ring!))))
                    have _conversion := Litex.sameDivIffSameMul _quotient.val.left _quotient.val.right _product.val.left _quotient.wd.1 _quotient.wd.2.1 _product.wd.1 _quotient.wd.2.2
                    exact (_conversion.mpr _child))))
                )
            )
          exact h_2
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_self_x5f_division_x2f_statement_x2e_lit
