import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_ranges_x5f_finite_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.Z (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.In _value_i2 (Litex.Z (M := M))), (by
  let _object_w2 := (Litex.closedRange _value_i1 _value_i2 h_16 h_17)
  let _object_w3 := (Litex.range _value_i1 _value_i2 h_16 h_17)
  exact (((by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.IsFiniteSet _atomic_wd_1_0)) ∧ ((by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.IsFiniteSet _atomic_wd_1_0)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i2 _rep_i2 _value_i2 h_17
          let _object_w2 := (Litex.closedRange _value_i1 _value_i2 h_16 h_17)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.IsFiniteSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.closedRangeFinite _atomic_wd_1_0))
                )
            )
          let _object_w3 := (Litex.range _value_i1 _value_i2 h_16 h_17)
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w3
            exact Litex.IsFiniteSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact (Litex.rangeFinite _atomic_wd_1_0))
                )
            )
          exact (And.intro h_1 h_2)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_ranges_x5f_finite_x2f_statement_x2e_lit
