import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_min_x5f_max_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v9
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_16 : Litex.In _value_i2 (Litex.R (M := M))), (by
  let _object_w2 := (Litex.min _value_i1 _value_i2 h_15 h_16)
  let _object_w3 := (Litex.min _value_i2 _value_i1 h_16 h_15)
  exact (by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w3
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_15 _Host_i2 _rep_i2 _value_i2 h_16
          let _object_w2 := (Litex.min _value_i1 _value_i2 h_15 h_16)
          let _object_w3 := (Litex.min _value_i2 _value_i1 h_16 h_15)
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            let _equal_wd_1_1 := _object_w3
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  let _equal_wd_1_1 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.minMaxCommutative _equal_wd_1_0 _equal_wd_1_1 (Eq.refl _) (Eq.refl _))))
                )
            )
          exact h_1
        )
      )
  )

theorem h_46 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_60 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_61 : Litex.In _value_i4 (Litex.R (M := M))), (by
  let _object_w5 := (Litex.max _value_i3 _value_i4 h_60 h_61)
  let _object_w6 := (Litex.max _value_i4 _value_i3 h_61 h_60)
  exact (by
    let _equal_wd_1_0 := _object_w5
    let _equal_wd_1_1 := _object_w6
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_60 _Host_i4 _rep_i4 _value_i4 h_61
          let _object_w5 := (Litex.max _value_i3 _value_i4 h_60 h_61)
          let _object_w6 := (Litex.max _value_i4 _value_i3 h_61 h_60)
          have h_45 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w5;
                  let _equal_wd_1_1 := _object_w6;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.minMaxCommutative _equal_wd_1_0 _equal_wd_1_1 (Eq.refl _) (Eq.refl _))))
                )
            )
          exact h_45
        )
      )
  )

theorem h_92 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_105 : Litex.In _value_i5 (Litex.R (M := M))), (by
  let _object_w8 := (Litex.min _value_i5 _value_i5 h_105 h_105)
  let _object_w9 := (Litex.max _value_i5 _value_i5 h_105 h_105)
  exact (((by
    let _equal_wd_1_0 := _object_w8
    exact Litex.Same _equal_wd_1_0 _value_i5)) ∧ ((by
    let _equal_wd_1_0 := _object_w9
    exact Litex.Same _equal_wd_1_0 _value_i5)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_105
          let _object_w8 := (Litex.min _value_i5 _value_i5 h_105 h_105)
          have h_90 : (by
            let _equal_wd_1_0 := _object_w8
            exact Litex.Same _equal_wd_1_0 _value_i5) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w8;
                  (show Litex.Same _equal_wd_1_0 _value_i5 from (Litex.minMaxIdempotent _equal_wd_1_0 (Eq.refl _))))
                )
            )
          let _object_w9 := (Litex.max _value_i5 _value_i5 h_105 h_105)
          have h_91 : (by
            let _equal_wd_1_0 := _object_w9
            exact Litex.Same _equal_wd_1_0 _value_i5) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w9;
                  (show Litex.Same _equal_wd_1_0 _value_i5 from (Litex.minMaxIdempotent _equal_wd_1_0 (Eq.refl _))))
                )
            )
          exact (And.intro h_90 h_91)
        )
      )
  )

theorem h_133 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_146 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_147 : Litex.In _value_i7 (Litex.R (M := M))), (by
  let _object_w11 := (Litex.min _value_i6 _value_i7 h_146 h_147)
  let _object_w12 := (Litex.max _value_i6 _value_i7 h_146 h_147)
  have h_131 : (by
    let _atomic_wd_1_0 := _object_w12
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := _object_w12
            exact (by
              let _extremum := _atomic_wd_1_0
              exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2
            ))
        )
    )
  let _object_w13 := (let _wd_1_0 := _value_i6;
  let _wd_1_1 := _object_w12;
  (Litex.min _wd_1_0 _wd_1_1 h_146 (by
    let _atomic_wd_1_0 := _object_w12
    exact h_131)))
  exact (((by
    let _atomic_wd_1_0 := _object_w11
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w12
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w13
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_146 _Host_i7 _rep_i7 _value_i7 h_147
          let _object_w11 := (Litex.min _value_i6 _value_i7 h_146 h_147)
          have h_130 : (by
            let _atomic_wd_1_0 := _object_w11
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w11
                    exact (by
                      let _extremum := _atomic_wd_1_0
                      exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2
                    ))
                )
            )
          let _object_w12 := (Litex.max _value_i6 _value_i7 h_146 h_147)
          have h_131 : (by
            let _atomic_wd_1_0 := _object_w12
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w12
                    exact (by
                      let _extremum := _atomic_wd_1_0
                      exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2
                    ))
                )
            )
          let _object_w13 := (let _wd_1_0 := _value_i6;
          let _wd_1_1 := _object_w12;
          (Litex.min _wd_1_0 _wd_1_1 h_146 (by
            let _atomic_wd_1_0 := _object_w12
            exact h_131)))
          have h_132 : (by
            let _atomic_wd_1_0 := _object_w13
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w13
                    exact (by
                      let _extremum := _atomic_wd_1_0
                      exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2
                    ))
                )
            )
          exact (And.intro h_130 (And.intro h_131 h_132))
        )
      )
  )

theorem h_229 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_242 : Litex.In _value_i8 (Litex.Z (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_243 : Litex.In _value_i9 (Litex.Z (M := M))), (by
  let _object_w15 := (Litex.min _value_i8 _value_i9 (Litex.integerToReal _value_i8 h_242) (Litex.integerToReal _value_i9 h_243))
  let _object_w16 := (Litex.max _value_i8 _value_i9 (Litex.integerToReal _value_i8 h_242) (Litex.integerToReal _value_i9 h_243))
  exact (((by
    let _atomic_wd_1_0 := _object_w15
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w16
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 h_242 _Host_i9 _rep_i9 _value_i9 h_243
          let _object_w15 := (Litex.min _value_i8 _value_i9 (Litex.integerToReal _value_i8 h_242) (Litex.integerToReal _value_i9 h_243))
          have h_227 : (by
            let _atomic_wd_1_0 := _object_w15
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w15
                    exact (Litex.minMaxMember _atomic_wd_1_0 (Litex.Z (M := M)) h_242 h_243))
                )
            )
          let _object_w16 := (Litex.max _value_i8 _value_i9 (Litex.integerToReal _value_i8 h_242) (Litex.integerToReal _value_i9 h_243))
          have h_228 : (by
            let _atomic_wd_1_0 := _object_w16
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w16
                    exact (Litex.minMaxMember _atomic_wd_1_0 (Litex.Z (M := M)) h_242 h_243))
                )
            )
          exact (And.intro h_227 h_228)
        )
      )
  )

noncomputable def _object_i10 := (Litex.min (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
theorem h_350 : Litex.Same (_object_i10 (M := M)) (Litex.min (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.min (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))))
      )
  )

theorem h_351 : Litex.IsSet (_object_i10 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.isSet (_object_i10 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_min_x5f_max_x2f_statement_x2e_lit
