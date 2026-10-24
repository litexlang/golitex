import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_factorial_x5f_order_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.N (M := M))) (h_1 : Litex.Le _value_i1 _value_i2), (by
  let _object_w3 := (Litex.factorial _value_i1 h_16)
  let _object_w4 := (Litex.factorial _value_i2 h_18)
  exact (by
    let _atomic_wd_1_0 := _object_w3
    let _atomic_wd_1_1 := _object_w4
    exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i2 _rep_i2 _value_i2 h_18 h_1
          have h_17 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_16)
                )
            )
          have h_19 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_18)
                )
            )
          let _object_w3 := (Litex.factorial _value_i1 h_16)
          let _object_w4 := (Litex.factorial _value_i2 h_18)
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w3
            let _atomic_wd_1_1 := _object_w4
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    let _atomic_wd_1_1 := _object_w4
                    exact (Litex.factorialMonotone _atomic_wd_1_0 _atomic_wd_1_1 h_1))
                )
            )
          exact h_2
        )
      )
  )

theorem h_643 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_668 : Litex.In _value_i3 (Litex.NPos (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_672 : Litex.In _value_i4 (Litex.N (M := M))) (h_641 : Litex.Lt _value_i3 _value_i4), (by
  let _object_w8 := (Litex.factorial _value_i3 (Litex.inNPos_natural _value_i3 h_668))
  let _object_w9 := (Litex.factorial _value_i4 h_672)
  exact (by
    let _atomic_wd_1_0 := _object_w8
    let _atomic_wd_1_1 := _object_w9
    exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_668 _Host_i4 _rep_i4 _value_i4 h_672 h_641
          have h_669 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i3 h_668)
                )
            )
          have h_670 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_669)
                )
            )
          have h_671 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_669) _litex_zero.symm)
                )
            )
          have h_673 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i4 h_672)
                )
            )
          have h_721 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i3 _value_i4 h_670 h_641)
                )
            )
          let _object_w8 := (Litex.factorial _value_i3 (Litex.inNPos_natural _value_i3 h_668))
          let _object_w9 := (Litex.factorial _value_i4 h_672)
          have h_642 : (by
            let _atomic_wd_1_0 := _object_w8
            let _atomic_wd_1_1 := _object_w9
            exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w8
                    let _atomic_wd_1_1 := _object_w9
                    exact (Litex.factorialStrictMonotone _atomic_wd_1_0 _atomic_wd_1_1 h_668 h_641))
                )
            )
          exact h_642
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_factorial_x5f_order_x2f_statement_x2e_lit
