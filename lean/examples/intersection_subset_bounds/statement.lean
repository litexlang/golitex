import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_intersection_x5f_subset_x5f_bounds_x2f_statement_x2e_lit

universe u v1 v2 v5 v6 v7 v10 v11 v12 v15 v16 v17
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_5 : Litex.IsSet _value_i2), (by
  let _object_w1 := (Litex.intersect _value_i1 _value_i2)
  exact (((by
    let _atomic_wd_1_0 := _object_w1
    exact Litex.Subset _atomic_wd_1_0 _value_i1)) ∧ ((by
    let _atomic_wd_1_0 := _object_w1
    exact Litex.Subset _atomic_wd_1_0 _value_i2)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_5
          let _object_w1 := (Litex.intersect _value_i1 _value_i2)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w1
            exact Litex.Subset _atomic_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w1
                    exact (Litex.intersectSubsetLeft _value_i1 _value_i2))
                )
            )
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w1
            exact Litex.Subset _atomic_wd_1_0 _value_i2) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w1
                    exact (Litex.intersectSubsetRight _value_i1 _value_i2))
                )
            )
          exact (And.intro h_1 h_2)
        )
      )
  )

theorem h_22 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_23 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_24 : Litex.IsSet _value_i6) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_25 : Litex.IsSet _value_i7) (h_20 : Litex.Subset _value_i5 _value_i7), (by
  let _object_w2 := (Litex.intersect _value_i5 _value_i6)
  exact (by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.Subset _atomic_wd_1_0 _value_i7)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_23 _Host_i6 _rep_i6 _value_i6 h_24 _Host_i7 _rep_i7 _value_i7 h_25 h_20
          let _object_w2 := (Litex.intersect _value_i5 _value_i6)
          have h_21 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.Subset _atomic_wd_1_0 _value_i7) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.intersectSubsetOfLeft _value_i5 _value_i6 _value_i7 h_20))
                )
            )
          exact h_21
        )
      )
  )

theorem h_43 : ∀ {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_45 : Litex.IsSet _value_i10) {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_46 : Litex.IsSet _value_i11) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_47 : Litex.IsSet _value_i12) (h_41 : Litex.Subset _value_i11 _value_i12), (by
  let _object_w3 := (Litex.intersect _value_i10 _value_i11)
  exact (by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.Subset _atomic_wd_1_0 _value_i12)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_45 _Host_i11 _rep_i11 _value_i11 h_46 _Host_i12 _rep_i12 _value_i12 h_47 h_41
          let _object_w3 := (Litex.intersect _value_i10 _value_i11)
          have h_42 : (by
            let _atomic_wd_1_0 := _object_w3
            exact Litex.Subset _atomic_wd_1_0 _value_i12) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact (Litex.intersectSubsetOfRight _value_i10 _value_i11 _value_i12 h_41))
                )
            )
          exact h_42
        )
      )
  )

theorem h_71 : ∀ {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_72 : Litex.IsSet _value_i15) {_Host_i16 : Type v16} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_73 : Litex.IsSet _value_i16) {_Host_i17 : Type v17} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_74 : Litex.IsSet _value_i17) (h_68 : Litex.Subset _value_i17 _value_i15) (h_69 : Litex.Subset _value_i17 _value_i16), (by
  let _object_w4 := (Litex.intersect _value_i15 _value_i16)
  exact (by
    let _atomic_wd_1_1 := _object_w4
    exact Litex.Subset _value_i17 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i15 _rep_i15 _value_i15 h_72 _Host_i16 _rep_i16 _value_i16 h_73 _Host_i17 _rep_i17 _value_i17 h_74 h_68 h_69
          let _object_w4 := (Litex.intersect _value_i15 _value_i16)
          have h_70 : (by
            let _atomic_wd_1_1 := _object_w4
            exact Litex.Subset _value_i17 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w4
                    exact (Litex.subsetIntersect _value_i17 _value_i15 _value_i16 h_68 h_69))
                )
            )
          exact h_70
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_intersection_x5f_subset_x5f_bounds_x2f_statement_x2e_lit
