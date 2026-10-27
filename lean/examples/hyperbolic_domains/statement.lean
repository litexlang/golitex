import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_domains_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_18 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w2 := (Litex.sinh _value_i1 h_18)
  let _object_w3 := (Litex.cosh _value_i1 h_18)
  let _object_w6 := (Litex.tanh _value_i1 h_18)
  let _object_w7 := (Litex.sech _value_i1 h_18)
  exact (((by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w6
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w7
    exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M)))))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_18
          let _object_w2 := (Litex.sinh _value_i1 h_18)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.sinhInR _atomic_wd_1_0))
                )
            )
          let _object_w3 := (Litex.cosh _value_i1 h_18)
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w3
            exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact (Litex.coshInRPos _atomic_wd_1_0))
                )
            )
          have h_43 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_w3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _object_w3 h_2)
                )
            )
          have h_44 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _object_w3 h_43)
                )
            )
          have h_45 : ¬ Litex.Same _object_w3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _object_w3 h_43) _litex_zero.symm)
                )
            )
          let _object_w6 := (Litex.tanh _value_i1 h_18)
          have h_3 : (by
            let _atomic_wd_1_0 := _object_w6
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w6
                    exact (Litex.tanhInR _atomic_wd_1_0))
                )
            )
          let _object_w7 := (Litex.sech _value_i1 h_18)
          have h_4 : (by
            let _atomic_wd_1_0 := _object_w7
            exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w7
                    exact (Litex.sechInRPos _atomic_wd_1_0))
                )
            )
          have h_86 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_w7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _object_w7 h_4)
                )
            )
          have h_87 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _object_w7 h_86)
                )
            )
          have h_88 : ¬ Litex.Same _object_w7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _object_w7 h_86) _litex_zero.symm)
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 h_4)))
        )
      )
  )

theorem h_92 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_105 : Litex.In _value_i2 (Litex.R (M := M))) (h_89 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w10 := (Litex.coth _value_i2 h_105 h_89)
  let _object_w12 := (Litex.csch _value_i2 h_105 h_89)
  exact (((by
    let _atomic_wd_1_0 := _object_w10
    exact Litex.In _atomic_wd_1_0 (Litex.RStar (M := M)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w12
    exact Litex.In _atomic_wd_1_0 (Litex.RStar (M := M)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_105 h_89
          let _object_w10 := (Litex.coth _value_i2 h_105 h_89)
          have h_90 : (by
            let _atomic_wd_1_0 := _object_w10
            exact Litex.In _atomic_wd_1_0 (Litex.RStar (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w10
                    exact (Litex.cothInRStar _atomic_wd_1_0))
                )
            )
          have h_121 : ¬ Litex.Same _object_w10 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRStar_nonzero _object_w10 h_90)
                )
            )
          let _object_w12 := (Litex.csch _value_i2 h_105 h_89)
          have h_91 : (by
            let _atomic_wd_1_0 := _object_w12
            exact Litex.In _atomic_wd_1_0 (Litex.RStar (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w12
                    exact (Litex.cschInRStar _atomic_wd_1_0))
                )
            )
          have h_141 : ¬ Litex.Same _object_w12 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRStar_nonzero _object_w12 h_91)
                )
            )
          exact (And.intro h_90 h_91)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_domains_x2f_statement_x2e_lit
