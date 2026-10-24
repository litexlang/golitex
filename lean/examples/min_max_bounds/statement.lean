import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_min_x5f_max_x5f_bounds_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v9
variable {M : Litex.Semantics.{u}}

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_18 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_19 : Litex.In _value_i2 (Litex.R (M := M))), (by
  let _object_w2 := (Litex.min _value_i1 _value_i2 h_18 h_19)
  let _object_w3 := (Litex.max _value_i1 _value_i2 h_18 h_19)
  exact (((by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.Le _atomic_wd_1_0 _value_i1)) ∧ ((((by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.Le _atomic_wd_1_0 _value_i2)) ∧ ((((by
    let _atomic_wd_1_1 := _object_w3
    exact Litex.Le _value_i1 _atomic_wd_1_1)) ∧ ((by
    let _atomic_wd_1_1 := _object_w3
    exact Litex.Le _value_i2 _atomic_wd_1_1)))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_18 _Host_i2 _rep_i2 _value_i2 h_19
          let _object_w2 := (Litex.min _value_i1 _value_i2 h_18 h_19)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.Le _atomic_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.minLeOperands _atomic_wd_1_0).1)
                )
            )
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.Le _atomic_wd_1_0 _value_i2) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.minLeOperands _atomic_wd_1_0).2)
                )
            )
          let _object_w3 := (Litex.max _value_i1 _value_i2 h_18 h_19)
          have h_3 : (by
            let _atomic_wd_1_1 := _object_w3
            exact Litex.Le _value_i1 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w3
                    exact (Litex.operandsLeMax _atomic_wd_1_1).1)
                )
            )
          have h_4 : (by
            let _atomic_wd_1_1 := _object_w3
            exact Litex.Le _value_i2 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w3
                    exact (Litex.operandsLeMax _atomic_wd_1_1).2)
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 h_4)))
        )
      )
  )

theorem h_1256 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_1269 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_1270 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1271 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1272 : Litex.In _value_i6 (Litex.R (M := M))) (h_1252 : Litex.Le _value_i3 _value_i5) (h_1253 : Litex.Le _value_i4 _value_i6), (by
  let _object_w5 := (Litex.min _value_i3 _value_i4 h_1269 h_1270)
  let _object_w6 := (Litex.min _value_i5 _value_i6 h_1271 h_1272)
  let _object_w7 := (Litex.max _value_i3 _value_i4 h_1269 h_1270)
  let _object_w8 := (Litex.max _value_i5 _value_i6 h_1271 h_1272)
  exact (((by
    let _atomic_wd_1_0 := _object_w5
    let _atomic_wd_1_1 := _object_w6
    exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)) ∧ ((by
    let _atomic_wd_1_0 := _object_w7
    let _atomic_wd_1_1 := _object_w8
    exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_1269 _Host_i4 _rep_i4 _value_i4 h_1270 _Host_i5 _rep_i5 _value_i5 h_1271 _Host_i6 _rep_i6 _value_i6 h_1272 h_1252 h_1253
          let _object_w5 := (Litex.min _value_i3 _value_i4 h_1269 h_1270)
          let _object_w6 := (Litex.min _value_i5 _value_i6 h_1271 h_1272)
          have h_1254 : (by
            let _atomic_wd_1_0 := _object_w5
            let _atomic_wd_1_1 := _object_w6
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    let _atomic_wd_1_1 := _object_w6
                    exact (by
                      let _minmax_left := _atomic_wd_1_0
                      let _minmax_right := _atomic_wd_1_1
                      exact Litex.minMaxMonotone _minmax_left _minmax_right h_1252 h_1253
                    ))
                )
            )
          let _object_w7 := (Litex.max _value_i3 _value_i4 h_1269 h_1270)
          let _object_w8 := (Litex.max _value_i5 _value_i6 h_1271 h_1272)
          have h_1255 : (by
            let _atomic_wd_1_0 := _object_w7
            let _atomic_wd_1_1 := _object_w8
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w7
                    let _atomic_wd_1_1 := _object_w8
                    exact (by
                      let _minmax_left := _atomic_wd_1_0
                      let _minmax_right := _atomic_wd_1_1
                      exact Litex.minMaxMonotone _minmax_left _minmax_right h_1252 h_1253
                    ))
                )
            )
          exact (And.intro h_1254 h_1255)
        )
      )
  )

theorem h_3032 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_3045 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_3046 : Litex.In _value_i8 (Litex.R (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_3047 : Litex.In _value_i9 (Litex.R (M := M))) (h_3029 : Litex.Le _value_i7 _value_i8), (by
  let _object_w10 := (Litex.min _value_i7 _value_i9 h_3045 h_3047)
  let _object_w11 := (Litex.min _value_i8 _value_i9 h_3046 h_3047)
  let _object_w12 := (Litex.max _value_i9 _value_i7 h_3047 h_3045)
  let _object_w13 := (Litex.max _value_i9 _value_i8 h_3047 h_3046)
  exact (((by
    let _atomic_wd_1_0 := _object_w10
    let _atomic_wd_1_1 := _object_w11
    exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)) ∧ ((by
    let _atomic_wd_1_0 := _object_w12
    let _atomic_wd_1_1 := _object_w13
    exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_3045 _Host_i8 _rep_i8 _value_i8 h_3046 _Host_i9 _rep_i9 _value_i9 h_3047 h_3029
          let _object_w10 := (Litex.min _value_i7 _value_i9 h_3045 h_3047)
          let _object_w11 := (Litex.min _value_i8 _value_i9 h_3046 h_3047)
          have h_3030 : (by
            let _atomic_wd_1_0 := _object_w10
            let _atomic_wd_1_1 := _object_w11
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w10
                    let _atomic_wd_1_1 := _object_w11
                    exact (by
                      let _minmax_left := _atomic_wd_1_0
                      let _minmax_right := _atomic_wd_1_1
                      exact Litex.minMaxMonotone _minmax_left _minmax_right h_3029 (Litex.leRefl _minmax_left.val.right _minmax_left.wd.2)
                    ))
                )
            )
          let _object_w12 := (Litex.max _value_i9 _value_i7 h_3047 h_3045)
          let _object_w13 := (Litex.max _value_i9 _value_i8 h_3047 h_3046)
          have h_3031 : (by
            let _atomic_wd_1_0 := _object_w12
            let _atomic_wd_1_1 := _object_w13
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w12
                    let _atomic_wd_1_1 := _object_w13
                    exact (by
                      let _minmax_left := _atomic_wd_1_0
                      let _minmax_right := _atomic_wd_1_1
                      exact Litex.minMaxMonotone _minmax_left _minmax_right (Litex.leRefl _minmax_left.val.left _minmax_left.wd.1) h_3029
                    ))
                )
            )
          exact (And.intro h_3030 h_3031)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_min_x5f_max_x5f_bounds_x2f_statement_x2e_lit
