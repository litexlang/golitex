import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_exponential_x5f_logarithm_x5f_inverse_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w2 := (let _wd_1_0 := (Litex.exp _value_i1 h_15);
  (Litex.ln _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.exp _value_i1 h_15)
    exact (Litex.expInRPos _atomic_wd_1_0))))
  exact (by
    let _equal_wd_1_0 := _object_w2
    exact Litex.Same _equal_wd_1_0 _value_i1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15
          let _object_w2 := (let _wd_1_0 := (Litex.exp _value_i1 h_15);
          (Litex.ln _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.exp _value_i1 h_15)
            exact (Litex.expInRPos _atomic_wd_1_0))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (Litex.lnExp _equal_wd_1_0)))
                )
            )
          exact h_1
        )
      )
  )

theorem h_35 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_48 : Litex.In _value_i2 (Litex.RPos (M := M))), (by
  let _object_w5 := (let _wd_1_0 := (Litex.ln _value_i2 h_48);
  (Litex.exp _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.ln _value_i2 h_48)
    exact (Litex.lnInR _atomic_wd_1_0))))
  exact (by
    let _equal_wd_1_0 := _object_w5
    exact Litex.Same _equal_wd_1_0 _value_i2)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_48
          have h_49 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i2 h_48)
                )
            )
          have h_50 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_49)
                )
            )
          have h_51 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_49) _litex_zero.symm)
                )
            )
          let _object_w5 := (let _wd_1_0 := (Litex.ln _value_i2 h_48);
          (Litex.exp _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.ln _value_i2 h_48)
            exact (Litex.lnInR _atomic_wd_1_0))))
          have h_34 : (by
            let _equal_wd_1_0 := _object_w5
            exact Litex.Same _equal_wd_1_0 _value_i2) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w5;
                  (show Litex.Same _equal_wd_1_0 _value_i2 from (Litex.expLn _equal_wd_1_0 h_49)))
                )
            )
          exact h_34
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_exponential_x5f_logarithm_x5f_inverse_x2f_statement_x2e_lit
