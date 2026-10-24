import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_add_x5f_zero_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.C (M := M))), (by
  let _object_w2 := (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) h_15 (Litex.numberInC (M := M) (0 : ℂ)))
  exact (by
    let _equal_wd_1_0 := _object_w2
    exact Litex.Same _equal_wd_1_0 _value_i1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15
          let _object_w2 := (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) h_15 (Litex.numberInC (M := M) (0 : ℂ)))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 h_15) + (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i1 h_15) (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_15) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i1 h_15) (by ring!))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_add_x5f_zero_x2f_statement_x2e_lit
