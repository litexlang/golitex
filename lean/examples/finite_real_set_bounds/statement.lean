import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_real_x5f_set_x5f_bounds_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.IsFiniteSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9 : Litex.In _value_i2 _value_i1) (h_1 : Litex.IsNonempty _value_i1) (h_2 : Litex.Subset _value_i1 (Litex.R (M := M))), (by
  let _object_w2 := (Litex.finiteExtremum false _value_i1 h_8 h_1 h_2)
  let _object_w3 := (Litex.finiteExtremum true _value_i1 h_8 h_1 h_2)
  exact (((by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.Le _atomic_wd_1_0 _value_i2)) ∧ ((((by
    let _atomic_wd_1_1 := _object_w3
    exact Litex.Le _value_i2 _atomic_wd_1_1)) ∧ ((by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.In _atomic_wd_1_0 _value_i1)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8 _Host_i2 _rep_i2 _value_i2 h_9 h_1 h_2
          let _object_w2 := (Litex.finiteExtremum false _value_i1 h_8 h_1 h_2)
          have h_3 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.Le _atomic_wd_1_0 _value_i2) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.finiteExtremumBound _atomic_wd_1_0 _value_i2 h_9))
                )
            )
          let _object_w3 := (Litex.finiteExtremum true _value_i1 h_8 h_1 h_2)
          have h_4 : (by
            let _atomic_wd_1_1 := _object_w3
            exact Litex.Le _value_i2 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w3
                    exact (Litex.finiteExtremumBound _atomic_wd_1_1 _value_i2 h_9))
                )
            )
          have h_5 : (by
            let _atomic_wd_1_0 := _object_w3
            exact Litex.In _atomic_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact (Eq.mp (congrArg (M.mem (Litex.denote _atomic_wd_1_0)) (show @Eq M.Value _ _ from Eq.refl _)) (Litex.finiteExtremumInSet _atomic_wd_1_0)))
                )
            )
          exact (And.intro h_3 (And.intro h_4 h_5))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_real_x5f_set_x5f_bounds_x2f_statement_x2e_lit
