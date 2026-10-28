import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonunit_x5f_integer_x5f_power_x5f_below_x5f_one_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.RPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_10 : Litex.In _value_i2 (Litex.Z (M := M))) (h_1 : Litex.Lt _value_i1 (Litex.number (M := M) (1 : ℂ))) (h_2 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), (by
  have h_7 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i1 h_6)
        )
    )
  have h_9 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_7) _litex_zero.symm)
        )
    )
  exact ¬ Litex.Same (Litex.powInt _value_i1 _value_i2 (Classical.choose ((M.integer_members (Litex.denote _value_i2)).mp h_10)) (Litex.positiveRealToComplex _value_i1 h_6) h_10 h_9 (Classical.choose_spec ((M.integer_members (Litex.denote _value_i2)).mp h_10))) (Litex.number (M := M) (1 : ℂ))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_10 h_1 h_2
          have h_7 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i1 h_6)
                )
            )
          have h_8 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_7)
                )
            )
          have h_9 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_7) _litex_zero.symm)
                )
            )
          have h_40 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i1 (Litex.number (M := M) (1 : ℂ)) h_8 h_1)
                )
            )
          have h_1468 : Litex.In _value_i1 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_1472 : Litex.In _value_i2 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_1469 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i1 h_1468)
                )
            )
          have h_1470 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_1469)
                )
            )
          have h_1471 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_1469) _litex_zero.symm)
                )
            )
          have h_1502 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i1 (Litex.number (M := M) (1 : ℂ)) h_1470 h_1)
                )
            )
          let _object_w9 := (Litex.powInt _value_i1 _value_i2 (Classical.choose ((M.integer_members (Litex.denote _value_i2)).mp h_1472)) (Litex.positiveRealToComplex _value_i1 h_1468) h_1472 h_1471 (Classical.choose_spec ((M.integer_members (Litex.denote _value_i2)).mp h_1472)))

          have h_5 : (by
            let _atomic_wd_1_0 := _object_w9
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    exact (let _base_guard := (And.intro h_1469 (Litex.ltNotSame _value_i1 (Litex.number 1) h_1)); fun _litex_equal => (Litex.powerNonunitOfGuards _atomic_wd_1_0 _base_guard.1 _base_guard.2 h_1472 h_2) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))))))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w9
            exact h_5)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonunit_x5f_integer_x5f_power_x5f_below_x5f_one_x2f_statement_x2e_lit
