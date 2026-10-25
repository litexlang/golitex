import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_set_x5f_containment_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v9 v10 v11 v12 v17 v18 v19 v22 v23 v24
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_7 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_8 : Litex.IsSet _value_i3) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_9 : Litex.IsSet _value_i4) (h_1 : Litex.Subset _value_i1 _value_i4) (h_2 : Litex.Subset _value_i2 _value_i4) (h_3 : Litex.Subset _value_i3 _value_i4), (by
  let _object_w1 := (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
  let _wd_1_1 := _value_i3;
  (Litex.union _wd_1_0 _wd_1_1))
  exact (by
    let _atomic_wd_1_0 := _object_w1
    exact Litex.Subset _atomic_wd_1_0 _value_i4)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_7 _Host_i3 _rep_i3 _value_i3 h_8 _Host_i4 _rep_i4 _value_i4 h_9 h_1 h_2 h_3
          let _object_w1 := (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
          let _wd_1_1 := _value_i3;
          (Litex.union _wd_1_0 _wd_1_1))
          have h_4 : (by
            let _atomic_wd_1_0 := _object_w1
            exact Litex.Subset _atomic_wd_1_0 _value_i4) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w1
                    exact (let _union := _atomic_wd_1_0; Litex.unionSubsetOfBoth _union.val.left _union.val.right _value_i4 (by
                      let _atomic_wd_2_0 := (Litex.union _value_i1 _value_i2)
                      exact (let _union := _atomic_wd_2_0; Litex.unionSubsetOfBoth _union.val.left _union.val.right _value_i4 h_1 h_2)) h_3))
                )
            )
          exact h_4
        )
      )
  )

theorem h_88 : ∀ {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_89 : Litex.IsSet _value_i9) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_90 : Litex.IsSet _value_i10) {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_91 : Litex.IsSet _value_i11) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_92 : Litex.IsSet _value_i12) (h_84 : Litex.Subset _value_i9 _value_i12) (h_85 : Litex.Subset _value_i10 _value_i12), (by
  let _object_w2 := (let _wd_1_0 := (Litex.union _value_i9 _value_i10);
  let _wd_1_1 := _value_i11;
  (Litex.intersect _wd_1_0 _wd_1_1))
  let _object_w3 := (let _wd_1_0 := _value_i11;
  let _wd_1_1 := (Litex.union _value_i9 _value_i10);
  (Litex.intersect _wd_1_0 _wd_1_1))
  exact (((by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.Subset _atomic_wd_1_0 _value_i12)) ∧ ((by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.Subset _atomic_wd_1_0 _value_i12)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_89 _Host_i10 _rep_i10 _value_i10 h_90 _Host_i11 _rep_i11 _value_i11 h_91 _Host_i12 _rep_i12 _value_i12 h_92 h_84 h_85
          let _object_w2 := (let _wd_1_0 := (Litex.union _value_i9 _value_i10);
          let _wd_1_1 := _value_i11;
          (Litex.intersect _wd_1_0 _wd_1_1))
          have h_86 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.Subset _atomic_wd_1_0 _value_i12) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.intersectSubsetOfLeft (Litex.union _value_i9 _value_i10) _value_i11 _value_i12 (by
                      let _atomic_wd_2_0 := (Litex.union _value_i9 _value_i10)
                      exact (let _union := _atomic_wd_2_0; Litex.unionSubsetOfBoth _union.val.left _union.val.right _value_i12 h_84 h_85))))
                )
            )
          let _object_w3 := (let _wd_1_0 := _value_i11;
          let _wd_1_1 := (Litex.union _value_i9 _value_i10);
          (Litex.intersect _wd_1_0 _wd_1_1))
          have h_87 : (by
            let _atomic_wd_1_0 := _object_w3
            exact Litex.Subset _atomic_wd_1_0 _value_i12) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact (Litex.intersectSubsetOfRight _value_i11 (Litex.union _value_i9 _value_i10) _value_i12 (by
                      let _atomic_wd_2_0 := (Litex.union _value_i9 _value_i10)
                      exact (let _union := _atomic_wd_2_0; Litex.unionSubsetOfBoth _union.val.left _union.val.right _value_i12 h_84 h_85))))
                )
            )
          exact (And.intro h_86 h_87)
        )
      )
  )

theorem h_231 : ∀ {_Host_i17 : Type v17} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_232 : Litex.IsSet _value_i17) {_Host_i18 : Type v18} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_233 : Litex.IsSet _value_i18) {_Host_i19 : Type v19} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_234 : Litex.IsSet _value_i19) (h_229 : Litex.Subset _value_i17 _value_i19), (by
  let _object_w4 := (Litex.setMinus _value_i17 _value_i18)
  exact (by
    let _atomic_wd_1_0 := _object_w4
    exact Litex.Subset _atomic_wd_1_0 _value_i19)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i17 _rep_i17 _value_i17 h_232 _Host_i18 _rep_i18 _value_i18 h_233 _Host_i19 _rep_i19 _value_i19 h_234 h_229
          let _object_w4 := (Litex.setMinus _value_i17 _value_i18)
          have h_230 : (by
            let _atomic_wd_1_0 := _object_w4
            exact Litex.Subset _atomic_wd_1_0 _value_i19) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w4
                    exact (let _set := _atomic_wd_1_0; Litex.setMinusSubsetOfLeft _set.val.left _set.val.right _value_i19 h_229))
                )
            )
          exact h_230
        )
      )
  )

theorem h_253 : ∀ {_Host_i22 : Type v22} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (h_254 : Litex.IsSet _value_i22) {_Host_i23 : Type v23} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (h_255 : Litex.IsSet _value_i23) {_Host_i24 : Type v24} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (h_256 : Litex.IsSet _value_i24) (h_250 : Litex.Subset _value_i22 _value_i23) (h_251 : Litex.Subset _value_i23 _value_i24), Litex.Subset _value_i22 _value_i24 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i22 _rep_i22 _value_i22 h_254 _Host_i23 _rep_i23 _value_i23 h_255 _Host_i24 _rep_i24 _value_i24 h_256 h_250 h_251
          have h_252 : Litex.Subset _value_i22 _value_i24 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.subsetTrans _value_i22 _value_i23 _value_i24 h_250 h_251)
                )
            )
          exact h_252
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_set_x5f_containment_x2f_statement_x2e_lit
