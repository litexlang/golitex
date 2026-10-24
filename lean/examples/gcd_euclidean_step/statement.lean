import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_gcd_x5f_euclidean_x5f_step_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_27 : Litex.In _value_i1 (Litex.Z (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_28 : Litex.In _value_i2 (Litex.NPos (M := M))), (by
  have h_29 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inNPos_positive _value_i2 h_28)
        )
    )
  have h_31 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_29) _litex_zero.symm)
        )
    )
  let _object_w5 := (Litex.gcd _value_i1 _value_i2 h_27 (Litex.naturalToInteger _value_i2 (Litex.inNPos_natural _value_i2 h_28)) (by
    classical
    apply Classical.byContradiction
    intro _negative_disjunction
    have h_966 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inl _branch)))
          )
      )
    exact _negative_disjunction (Or.inr h_31)
  ))
  let _object_w6 := (let _wd_1_0 := _value_i2;
  let _wd_1_1 := (Litex.mod _value_i1 _wd_1_0 h_27 (Litex.naturalToInteger _wd_1_0 (Litex.inNPos_natural _wd_1_0 h_28)) h_31);
  (Litex.gcd _wd_1_0 _wd_1_1 (Litex.naturalToInteger _wd_1_0 (Litex.inNPos_natural _wd_1_0 h_28)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.modInZ _atomic_wd_1_0)) (by
    classical
    apply Classical.byContradiction
    intro _negative_disjunction
    have h_2457 : Litex.Same _wd_1_1 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
          )
      )
    exact _negative_disjunction (Or.inl h_31)
  )))
  exact (by
    let _equal_wd_1_0 := _object_w5
    let _equal_wd_1_1 := _object_w6
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_27 _Host_i2 _rep_i2 _value_i2 h_28
          have h_29 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i2 h_28)
                )
            )
          have h_30 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_29)
                )
            )
          have h_31 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_29) _litex_zero.symm)
                )
            )
          let _object_w5 := (Litex.gcd _value_i1 _value_i2 h_27 (Litex.naturalToInteger _value_i2 (Litex.inNPos_natural _value_i2 h_28)) (by
            classical
            apply Classical.byContradiction
            intro _negative_disjunction
            have h_966 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inl _branch)))
                  )
              )
            exact _negative_disjunction (Or.inr h_31)
          ))
          let _object_w6 := (let _wd_1_0 := _value_i2;
          let _wd_1_1 := (Litex.mod _value_i1 _wd_1_0 h_27 (Litex.naturalToInteger _wd_1_0 (Litex.inNPos_natural _wd_1_0 h_28)) h_31);
          (Litex.gcd _wd_1_0 _wd_1_1 (Litex.naturalToInteger _wd_1_0 (Litex.inNPos_natural _wd_1_0 h_28)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.modInZ _atomic_wd_1_0)) (by
            classical
            apply Classical.byContradiction
            intro _negative_disjunction
            have h_2457 : Litex.Same _wd_1_1 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
                  )
              )
            exact _negative_disjunction (Or.inl h_31)
          )))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w5;
                  let _equal_wd_1_1 := _object_w6;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.gcdEuclideanStep _equal_wd_1_0)))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_gcd_x5f_euclidean_x5f_step_x2f_statement_x2e_lit
