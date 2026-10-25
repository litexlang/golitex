import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_set_x5f_size_x5f_bounds_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.IsSet _value_i1) (h_1 : Litex.IsFiniteSet _value_i1), (by
  let _object_w1 := (Litex.finiteSetSize _value_i1 h_1)
  exact (((by
    let _atomic_wd_1_0 := _object_w1
    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w1
    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 h_1
          let _object_w1 := (Litex.finiteSetSize _value_i1 h_1)
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w1
            exact Litex.In _atomic_wd_1_0 (Litex.N (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w1
                    exact (Litex.finiteSetSizeInN _atomic_wd_1_0))
                )
            )
          have h_10 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _object_w1 h_2)
                )
            )
          have h_3 : (by
            let _atomic_wd_1_0 := _object_w1
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w1
                    exact h_10)
                )
            )
          exact (And.intro h_2 h_3)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_set_x5f_size_x5f_bounds_x2f_statement_x2e_lit
