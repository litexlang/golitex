import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_union_x5f_containment_x5f_bounds_x2f_statement_x2e_lit

universe u v1 v2 v3 v7 v8 v9 v10 v15 v16 v17 v21 v22 v23 v27 v28
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_7 : Litex.IsSet _value_i3) (h_1 : Litex.Subset _value_i1 _value_i3) (h_2 : Litex.Subset _value_i2 _value_i3), (by
  let _object_w1 := (Litex.union _value_i1 _value_i2)
  exact (by
    let _atomic_wd_1_0 := _object_w1
    exact Litex.Subset _atomic_wd_1_0 _value_i3)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_6 _Host_i3 _rep_i3 _value_i3 h_7 h_1 h_2
          let _object_w1 := (Litex.union _value_i1 _value_i2)
          have h_3 : (by
            let _atomic_wd_1_0 := _object_w1
            exact Litex.Subset _atomic_wd_1_0 _value_i3) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w1
                    exact (let _union := _atomic_wd_1_0; Litex.unionSubsetOfBoth _union.val.left _union.val.right _value_i3 h_1 h_2))
                )
            )
          exact h_3
        )
      )
  )

theorem h_42 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_43 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_44 : Litex.IsSet _value_i8) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_45 : Litex.IsSet _value_i9) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_46 : Litex.IsSet _value_i10) (h_38 : Litex.Subset _value_i7 _value_i9) (h_39 : Litex.Subset _value_i8 _value_i10), (by
  let _object_w2 := (Litex.union _value_i7 _value_i8)
  let _object_w3 := (Litex.union _value_i9 _value_i10)
  let _object_w4 := (Litex.union _value_i10 _value_i9)
  exact (((by
    let _atomic_wd_1_0 := _object_w2
    let _atomic_wd_1_1 := _object_w3
    exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1)) ∧ ((by
    let _atomic_wd_1_0 := _object_w2
    let _atomic_wd_1_1 := _object_w4
    exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_43 _Host_i8 _rep_i8 _value_i8 h_44 _Host_i9 _rep_i9 _value_i9 h_45 _Host_i10 _rep_i10 _value_i10 h_46 h_38 h_39
          let _object_w2 := (Litex.union _value_i7 _value_i8)
          let _object_w3 := (Litex.union _value_i9 _value_i10)
          have h_40 : (by
            let _atomic_wd_1_0 := _object_w2
            let _atomic_wd_1_1 := _object_w3
            exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    let _atomic_wd_1_1 := _object_w3
                    exact (let _subset_left := _atomic_wd_1_0; let _subset_right := _atomic_wd_1_1; Litex.unionMono _subset_left.val.left _subset_left.val.right _subset_right.val.left _subset_right.val.right h_38 h_39))
                )
            )
          let _object_w4 := (Litex.union _value_i10 _value_i9)
          have h_41 : (by
            let _atomic_wd_1_0 := _object_w2
            let _atomic_wd_1_1 := _object_w4
            exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    let _atomic_wd_1_1 := _object_w4
                    exact (let _subset_left := _atomic_wd_1_0; let _subset_right := _atomic_wd_1_1; Litex.unionMonoSwap _subset_left.val.left _subset_left.val.right _subset_right.val.left _subset_right.val.right h_38 h_39))
                )
            )
          exact (And.intro h_40 h_41)
        )
      )
  )

theorem h_128 : ∀ {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_129 : Litex.IsSet _value_i15) {_Host_i16 : Type v16} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_130 : Litex.IsSet _value_i16) {_Host_i17 : Type v17} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_131 : Litex.IsSet _value_i17) (h_125 : Litex.Subset _value_i15 _value_i16), (by
  let _object_w5 := (Litex.union _value_i17 _value_i15)
  let _object_w6 := (Litex.union _value_i17 _value_i16)
  let _object_w7 := (Litex.union _value_i16 _value_i17)
  exact (((by
    let _atomic_wd_1_0 := _object_w5
    let _atomic_wd_1_1 := _object_w6
    exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1)) ∧ ((by
    let _atomic_wd_1_0 := _object_w5
    let _atomic_wd_1_1 := _object_w7
    exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i15 _rep_i15 _value_i15 h_129 _Host_i16 _rep_i16 _value_i16 h_130 _Host_i17 _rep_i17 _value_i17 h_131 h_125
          let _object_w5 := (Litex.union _value_i17 _value_i15)
          let _object_w6 := (Litex.union _value_i17 _value_i16)
          have h_126 : (by
            let _atomic_wd_1_0 := _object_w5
            let _atomic_wd_1_1 := _object_w6
            exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    let _atomic_wd_1_1 := _object_w6
                    exact (let _subset_left := _atomic_wd_1_0; let _subset_right := _atomic_wd_1_1; Litex.unionMono _subset_left.val.left _subset_left.val.right _subset_right.val.left _subset_right.val.right (Litex.subsetRefl _subset_left.val.left) h_125))
                )
            )
          let _object_w7 := (Litex.union _value_i16 _value_i17)
          have h_127 : (by
            let _atomic_wd_1_0 := _object_w5
            let _atomic_wd_1_1 := _object_w7
            exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    let _atomic_wd_1_1 := _object_w7
                    exact (let _subset_left := _atomic_wd_1_0; let _subset_right := _atomic_wd_1_1; Litex.unionMonoSwap _subset_left.val.left _subset_left.val.right _subset_right.val.left _subset_right.val.right (Litex.subsetRefl _subset_left.val.left) h_125))
                )
            )
          exact (And.intro h_126 h_127)
        )
      )
  )

theorem h_179 : ∀ {_Host_i21 : Type v21} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (h_182 : Litex.IsSet _value_i21) {_Host_i22 : Type v22} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (h_183 : Litex.IsSet _value_i22) {_Host_i23 : Type v23} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (h_184 : Litex.IsSet _value_i23) (h_176 : Litex.Subset _value_i21 _value_i22), (by
  let _object_w8 := (Litex.union _value_i21 _value_i23)
  let _object_w9 := (Litex.union _value_i22 _value_i23)
  let _object_w10 := (Litex.union _value_i23 _value_i22)
  exact (((by
    let _atomic_wd_1_0 := _object_w8
    let _atomic_wd_1_1 := _object_w9
    exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1)) ∧ ((by
    let _atomic_wd_1_0 := _object_w8
    let _atomic_wd_1_1 := _object_w10
    exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i21 _rep_i21 _value_i21 h_182 _Host_i22 _rep_i22 _value_i22 h_183 _Host_i23 _rep_i23 _value_i23 h_184 h_176
          let _object_w8 := (Litex.union _value_i21 _value_i23)
          let _object_w9 := (Litex.union _value_i22 _value_i23)
          have h_177 : (by
            let _atomic_wd_1_0 := _object_w8
            let _atomic_wd_1_1 := _object_w9
            exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w8
                    let _atomic_wd_1_1 := _object_w9
                    exact (let _subset_left := _atomic_wd_1_0; let _subset_right := _atomic_wd_1_1; Litex.unionMono _subset_left.val.left _subset_left.val.right _subset_right.val.left _subset_right.val.right h_176 (Litex.subsetRefl _subset_left.val.right)))
                )
            )
          let _object_w10 := (Litex.union _value_i23 _value_i22)
          have h_178 : (by
            let _atomic_wd_1_0 := _object_w8
            let _atomic_wd_1_1 := _object_w10
            exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w8
                    let _atomic_wd_1_1 := _object_w10
                    exact (let _subset_left := _atomic_wd_1_0; let _subset_right := _atomic_wd_1_1; Litex.unionMonoSwap _subset_left.val.left _subset_left.val.right _subset_right.val.left _subset_right.val.right h_176 (Litex.subsetRefl _subset_left.val.right)))
                )
            )
          exact (And.intro h_177 h_178)
        )
      )
  )

theorem h_234 : ∀ {_Host_i27 : Type v27} [_rep_i27 : Litex.Representation M _Host_i27] (_value_i27 : Litex.Obj (M := M) _Host_i27) (h_235 : Litex.IsSet _value_i27) {_Host_i28 : Type v28} [_rep_i28 : Litex.Representation M _Host_i28] (_value_i28 : Litex.Obj (M := M) _Host_i28) (h_236 : Litex.IsSet _value_i28), (by
  let _object_w11 := (Litex.union _value_i27 _value_i28)
  let _object_w12 := (Litex.union _value_i28 _value_i27)
  exact (by
    let _atomic_wd_1_0 := _object_w11
    let _atomic_wd_1_1 := _object_w12
    exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i27 _rep_i27 _value_i27 h_235 _Host_i28 _rep_i28 _value_i28 h_236
          let _object_w11 := (Litex.union _value_i27 _value_i28)
          let _object_w12 := (Litex.union _value_i28 _value_i27)
          have h_233 : (by
            let _atomic_wd_1_0 := _object_w11
            let _atomic_wd_1_1 := _object_w12
            exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w11
                    let _atomic_wd_1_1 := _object_w12
                    exact (let _subset_left := _atomic_wd_1_0; let _subset_right := _atomic_wd_1_1; Litex.unionMonoSwap _subset_left.val.left _subset_left.val.right _subset_right.val.left _subset_right.val.right (Litex.subsetRefl _subset_left.val.left) (Litex.subsetRefl _subset_left.val.right)))
                )
            )
          exact h_233
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_union_x5f_containment_x5f_bounds_x2f_statement_x2e_lit
