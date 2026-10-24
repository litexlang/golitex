import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_rounding_x5f_bounds_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}

theorem h_7 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_20 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w2 := (Litex.floor _value_i1 h_20)
  have h_1 : (by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := _object_w2
            exact (Litex.roundingInZ _atomic_wd_1_0))
        )
    )
  let _object_w4 := (Litex.ceil _value_i1 h_20)
  have h_2 : (by
    let _atomic_wd_1_0 := _object_w4
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := _object_w4
            exact (Litex.roundingInZ _atomic_wd_1_0))
        )
    )
  let _object_w5 := (let _wd_1_0 := _object_w2;
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _object_w2
    exact (Litex.integerToComplex _atomic_wd_1_0 h_1)) (Litex.numberInC (M := M) (1 : ℂ))))
  let _object_w6 := (let _wd_1_0 := _object_w4;
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (Litex.sub _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _object_w4
    exact (Litex.integerToComplex _atomic_wd_1_0 h_2)) (Litex.numberInC (M := M) (1 : ℂ))))
  exact (((by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w4
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.Le _atomic_wd_1_0 _value_i1)) ∧ ((((by
    let _atomic_wd_1_1 := _object_w5
    exact Litex.Lt _value_i1 _atomic_wd_1_1)) ∧ ((((by
    let _atomic_wd_1_0 := _object_w6
    exact Litex.Lt _atomic_wd_1_0 _value_i1)) ∧ ((by
    let _atomic_wd_1_1 := _object_w4
    exact Litex.Le _value_i1 _atomic_wd_1_1)))))))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_20
          let _object_w2 := (Litex.floor _value_i1 h_20)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.roundingInZ _atomic_wd_1_0))
                )
            )
          let _object_w4 := (Litex.ceil _value_i1 h_20)
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w4
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w4
                    exact (Litex.roundingInZ _atomic_wd_1_0))
                )
            )
          have h_3 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.Le _atomic_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.floorLeArgument _atomic_wd_1_0))
                )
            )
          let _object_w5 := (let _wd_1_0 := _object_w2;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w2
            exact (Litex.integerToComplex _atomic_wd_1_0 h_1)) (Litex.numberInC (M := M) (1 : ℂ))))
          have h_4 : (by
            let _atomic_wd_1_1 := _object_w5
            exact Litex.Lt _value_i1 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w5
                    exact (Litex.floorStrictUpper _atomic_wd_1_1 (Litex.sameRefl (Litex.number (M := M) 1))))
                )
            )
          let _object_w6 := (let _wd_1_0 := _object_w4;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w4
            exact (Litex.integerToComplex _atomic_wd_1_0 h_2)) (Litex.numberInC (M := M) (1 : ℂ))))
          have h_5 : (by
            let _atomic_wd_1_0 := _object_w6
            exact Litex.Lt _atomic_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w6
                    exact (Litex.ceilStrictLower _atomic_wd_1_0 (Litex.sameRefl (Litex.number (M := M) 1))))
                )
            )
          have h_6 : (by
            let _atomic_wd_1_1 := _object_w4
            exact Litex.Le _value_i1 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w4
                    exact (Litex.argumentLeCeil _atomic_wd_1_1))
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 (And.intro h_4 (And.intro h_5 h_6)))))
        )
      )
  )

theorem h_429 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_442 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_443 : Litex.In _value_i3 (Litex.R (M := M))) (h_426 : Litex.Le _value_i2 _value_i3), (by
  let _object_w8 := (Litex.floor _value_i2 h_442)
  let _object_w9 := (Litex.floor _value_i3 h_443)
  let _object_w10 := (Litex.ceil _value_i2 h_442)
  let _object_w11 := (Litex.ceil _value_i3 h_443)
  exact (((by
    let _atomic_wd_1_0 := _object_w8
    let _atomic_wd_1_1 := _object_w9
    exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)) ∧ ((by
    let _atomic_wd_1_0 := _object_w10
    let _atomic_wd_1_1 := _object_w11
    exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_442 _Host_i3 _rep_i3 _value_i3 h_443 h_426
          let _object_w8 := (Litex.floor _value_i2 h_442)
          let _object_w9 := (Litex.floor _value_i3 h_443)
          have h_427 : (by
            let _atomic_wd_1_0 := _object_w8
            let _atomic_wd_1_1 := _object_w9
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w8
                    let _atomic_wd_1_1 := _object_w9
                    exact (Litex.roundingMonotone _atomic_wd_1_0 _atomic_wd_1_1 h_426))
                )
            )
          let _object_w10 := (Litex.ceil _value_i2 h_442)
          let _object_w11 := (Litex.ceil _value_i3 h_443)
          have h_428 : (by
            let _atomic_wd_1_0 := _object_w10
            let _atomic_wd_1_1 := _object_w11
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w10
                    let _atomic_wd_1_1 := _object_w11
                    exact (Litex.roundingMonotone _atomic_wd_1_0 _atomic_wd_1_1 h_426))
                )
            )
          exact (And.intro h_427 h_428)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_rounding_x5f_bounds_x2f_statement_x2e_lit
