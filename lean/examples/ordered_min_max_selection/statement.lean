import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_min_x5f_max_x5f_selection_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_20 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : Litex.Le _value_i1 _value_i2), (by
  let _object_w2 := (Litex.min _value_i1 _value_i2 h_19 h_20)
  let _object_w3 := (Litex.min _value_i2 _value_i1 h_20 h_19)
  let _object_w4 := (Litex.max _value_i1 _value_i2 h_19 h_20)
  let _object_w5 := (Litex.max _value_i2 _value_i1 h_20 h_19)
  exact (((by
    let _equal_wd_1_0 := _object_w2
    exact Litex.Same _equal_wd_1_0 _value_i1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w3
    exact Litex.Same _equal_wd_1_0 _value_i1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w4
    exact Litex.Same _equal_wd_1_0 _value_i2)) ∧ ((by
    let _equal_wd_1_0 := _object_w5
    exact Litex.Same _equal_wd_1_0 _value_i2)))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_19 _Host_i2 _rep_i2 _value_i2 h_20 h_1
          let _object_w2 := (Litex.min _value_i1 _value_i2 h_19 h_20)
          have h_2 : (by
            let _equal_wd_1_0 := _object_w2
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (Litex.minOfLeOperands _equal_wd_1_0 h_1)))
                )
            )
          let _object_w3 := (Litex.min _value_i2 _value_i1 h_20 h_19)
          have h_3 : (by
            let _equal_wd_1_0 := _object_w3
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (Litex.minOfGeOperands _equal_wd_1_0 h_1)))
                )
            )
          let _object_w4 := (Litex.max _value_i1 _value_i2 h_19 h_20)
          have h_4 : (by
            let _equal_wd_1_0 := _object_w4
            exact Litex.Same _equal_wd_1_0 _value_i2) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w4;
                  (show Litex.Same _equal_wd_1_0 _value_i2 from (Litex.maxOfLeOperands _equal_wd_1_0 h_1)))
                )
            )
          let _object_w5 := (Litex.max _value_i2 _value_i1 h_20 h_19)
          have h_5 : (by
            let _equal_wd_1_0 := _object_w5
            exact Litex.Same _equal_wd_1_0 _value_i2) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w5;
                  (show Litex.Same _equal_wd_1_0 _value_i2 from (Litex.maxOfGeOperands _equal_wd_1_0 h_1)))
                )
            )
          exact (And.intro h_2 (And.intro h_3 (And.intro h_4 h_5)))
        )
      )
  )

theorem h_154 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_169 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_170 : Litex.In _value_i4 (Litex.R (M := M))) (h_149 : Litex.Le _value_i3 _value_i4), (by
  let _object_w7 := (Litex.min _value_i3 _value_i4 h_169 h_170)
  let _object_w8 := (Litex.min _value_i4 _value_i3 h_170 h_169)
  let _object_w9 := (Litex.max _value_i3 _value_i4 h_169 h_170)
  let _object_w10 := (Litex.max _value_i4 _value_i3 h_170 h_169)
  exact (((by
    let _equal_wd_1_1 := _object_w7
    exact Litex.Same _value_i3 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_1 := _object_w8
    exact Litex.Same _value_i3 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_1 := _object_w9
    exact Litex.Same _value_i4 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_1 := _object_w10
    exact Litex.Same _value_i4 _equal_wd_1_1)))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_169 _Host_i4 _rep_i4 _value_i4 h_170 h_149
          let _object_w7 := (Litex.min _value_i3 _value_i4 h_169 h_170)
          have h_150 : (by
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _value_i3 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_1 := _object_w7;
                  (show Litex.Same _value_i3 _equal_wd_1_1 from (Litex.minOfLeOperands _equal_wd_1_1 h_149).symm))
                )
            )
          let _object_w8 := (Litex.min _value_i4 _value_i3 h_170 h_169)
          have h_151 : (by
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _value_i3 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_1 := _object_w8;
                  (show Litex.Same _value_i3 _equal_wd_1_1 from (Litex.minOfGeOperands _equal_wd_1_1 h_149).symm))
                )
            )
          let _object_w9 := (Litex.max _value_i3 _value_i4 h_169 h_170)
          have h_152 : (by
            let _equal_wd_1_1 := _object_w9
            exact Litex.Same _value_i4 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_1 := _object_w9;
                  (show Litex.Same _value_i4 _equal_wd_1_1 from (Litex.maxOfLeOperands _equal_wd_1_1 h_149).symm))
                )
            )
          let _object_w10 := (Litex.max _value_i4 _value_i3 h_170 h_169)
          have h_153 : (by
            let _equal_wd_1_1 := _object_w10
            exact Litex.Same _value_i4 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_1 := _object_w10;
                  (show Litex.Same _value_i4 _equal_wd_1_1 from (Litex.maxOfGeOperands _equal_wd_1_1 h_149).symm))
                )
            )
          exact (And.intro h_150 (And.intro h_151 (And.intro h_152 h_153)))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_min_x5f_max_x5f_selection_x2f_statement_x2e_lit
