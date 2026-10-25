import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_interval_x5f_membership_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_19 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : Litex.Lt _value_i1 _value_i3) (h_2 : Litex.Le _value_i3 _value_i2), (by
  let _object_w2 := (Litex.realInterval false true _value_i1 _value_i2 h_17 h_18)
  exact (by
    let _atomic_wd_1_1 := _object_w2
    exact Litex.In _value_i3 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 _Host_i3 _rep_i3 _value_i3 h_19 h_1 h_2
          let _object_w2 := (Litex.realInterval false true _value_i1 _value_i2 h_17 h_18)
          have h_3 : (by
            let _atomic_wd_1_1 := _object_w2
            exact Litex.In _value_i3 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w2
                    exact ((Litex.inRealInterval_iff _atomic_wd_1_1 _value_i3).mpr ⟨h_19, h_1, h_2⟩))
                )
            )
          have h_160 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealInterval_iff _object_w2 _value_i3).mp h_3).1
                )
            )
          have h_161 : Litex.Lt _value_i1 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealInterval_iff _object_w2 _value_i3).mp h_3).2.1
                )
            )
          have h_162 : Litex.Le _value_i3 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealInterval_iff _object_w2 _value_i3).mp h_3).2.2
                )
            )
          exact h_3
        )
      )
  )

theorem h_165 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_178 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_179 : Litex.In _value_i5 (Litex.R (M := M))) (h_163 : Litex.Lt _value_i4 _value_i5), (by
  let _object_w4 := (Litex.realRay true false _value_i4 h_178)
  exact (by
    let _atomic_wd_1_1 := _object_w4
    exact Litex.In _value_i5 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_178 _Host_i5 _rep_i5 _value_i5 h_179 h_163
          let _object_w4 := (Litex.realRay true false _value_i4 h_178)
          have h_164 : (by
            let _atomic_wd_1_1 := _object_w4
            exact Litex.In _value_i5 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w4
                    exact ((Litex.inRealRay_iff _atomic_wd_1_1 _value_i5).mpr ⟨h_179, h_163⟩))
                )
            )
          have h_232 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealRay_iff _object_w4 _value_i5).mp h_164).1
                )
            )
          have h_233 : Litex.Lt _value_i4 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealRay_iff _object_w4 _value_i5).mp h_164).2
                )
            )
          exact h_164
        )
      )
  )

theorem h_236 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_250 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_251 : Litex.In _value_i7 (Litex.R (M := M))) (h_234 : Litex.Le _value_i7 _value_i6), (by
  let _object_w6 := (Litex.realRay false true _value_i6 h_250)
  exact (by
    let _atomic_wd_1_1 := _object_w6
    exact Litex.In _value_i7 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_250 _Host_i7 _rep_i7 _value_i7 h_251 h_234
          let _object_w6 := (Litex.realRay false true _value_i6 h_250)
          have h_235 : (by
            let _atomic_wd_1_1 := _object_w6
            exact Litex.In _value_i7 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w6
                    exact ((Litex.inRealRay_iff _atomic_wd_1_1 _value_i7).mpr ⟨h_251, h_234⟩))
                )
            )
          have h_333 : Litex.In _value_i7 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealRay_iff _object_w6 _value_i7).mp h_235).1
                )
            )
          have h_334 : Litex.Le _value_i7 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealRay_iff _object_w6 _value_i7).mp h_235).2
                )
            )
          exact h_235
        )
      )
  )

theorem h_337 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_350 : Litex.In _value_i8 (Litex.R (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_351 : Litex.In _value_i9 (Litex.R (M := M))) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_352 : Litex.In _value_i10 (Litex.R (M := M))) (h_335 : Litex.Lt _value_i10 _value_i8), (by
  let _object_w8 := (Litex.realInterval true true _value_i8 _value_i9 h_350 h_351)
  exact (by
    let _atomic_wd_1_1 := _object_w8
    exact ¬ Litex.In _value_i10 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 h_350 _Host_i9 _rep_i9 _value_i9 h_351 _Host_i10 _rep_i10 _value_i10 h_352 h_335
          let _object_w8 := (Litex.realInterval true true _value_i8 _value_i9 h_350 h_351)
          have h_336 : (by
            let _atomic_wd_1_1 := _object_w8
            exact ¬ Litex.In _value_i10 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w8
                    exact (Litex.notInRealIntervalLower _atomic_wd_1_1 _value_i10 h_335))
                )
            )
          exact h_336
        )
      )
  )

theorem h_403 : ∀ {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_419 : Litex.In _value_i11 (Litex.R (M := M))) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_420 : Litex.In _value_i12 (Litex.R (M := M))) (h_401 : Litex.Le _value_i12 _value_i11), (by
  let _object_w10 := (Litex.realRay true false _value_i11 h_419)
  exact (by
    let _atomic_wd_1_1 := _object_w10
    exact ¬ Litex.In _value_i12 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i11 _rep_i11 _value_i11 h_419 _Host_i12 _rep_i12 _value_i12 h_420 h_401
          let _object_w10 := (Litex.realRay true false _value_i11 h_419)
          have h_402 : (by
            let _atomic_wd_1_1 := _object_w10
            exact ¬ Litex.In _value_i12 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w10
                    exact (Litex.notInRealRayOpposite _atomic_wd_1_1 _value_i12 h_401))
                )
            )
          exact h_402
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_interval_x5f_membership_x2f_statement_x2e_lit
