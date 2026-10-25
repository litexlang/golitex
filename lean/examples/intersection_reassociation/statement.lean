import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_intersection_x5f_reassociation_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_7 : Litex.IsSet _value_i3) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_8 : Litex.In _value_i4 (let _wd_1_0 := (Litex.intersect _value_i1 _value_i2);
let _wd_1_1 := _value_i3;
(Litex.intersect _wd_1_0 _wd_1_1))), (by
  let _atomic_wd_1_1 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.intersect _value_i2 _value_i3);
  (Litex.intersect _wd_1_0 _wd_1_1))
  exact Litex.In _value_i4 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_6 _Host_i3 _rep_i3 _value_i3 h_7 _Host_i4 _rep_i4 _value_i4 h_8
          have h_9 : Litex.In _value_i4 (Litex.intersect _value_i1 _value_i2) :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff _value_i4 (Litex.intersect _value_i1 _value_i2) _value_i3).mp h_8).1)
                )
            )
          have h_10 : Litex.In _value_i4 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff _value_i4 (Litex.intersect _value_i1 _value_i2) _value_i3).mp h_8).2)
                )
            )
          have h_17 : Litex.IsSet _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          have h_18 : Litex.IsSet _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_19 : Litex.IsSet _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_20 : Litex.In _value_i4 (let _wd_1_0 := (Litex.intersect _value_i1 _value_i2);
          let _wd_1_1 := _value_i3;
          (Litex.intersect _wd_1_0 _wd_1_1)) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_21 : Litex.In _value_i4 (Litex.intersect _value_i1 _value_i2) :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff _value_i4 (Litex.intersect _value_i1 _value_i2) _value_i3).mp h_20).1)
                )
            )
          have h_22 : Litex.In _value_i4 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff _value_i4 (Litex.intersect _value_i1 _value_i2) _value_i3).mp h_20).2)
                )
            )
          have h_3 : (by
            let _atomic_wd_1_1 := (Litex.intersect _value_i1 _value_i2)
            exact Litex.In _value_i4 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (Litex.intersect _value_i1 _value_i2)
                    exact h_21)
                )
            )

          have h_31 : Litex.In _value_i4 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff _value_i4 _value_i1 _value_i2).mp h_3).1)
                )
            )

          have h_32 : Litex.In _value_i4 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff _value_i4 _value_i1 _value_i2).mp h_3).2)
                )
            )
          let _object_w5 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.intersect _value_i2 _value_i3);
          (Litex.intersect _wd_1_0 _wd_1_1))

          have h_4 : (by
            let _atomic_wd_1_1 := _object_w5
            exact Litex.In _value_i4 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w5
                    exact ((Litex.inIntersect_iff _value_i4 _value_i1 (Litex.intersect _value_i2 _value_i3)).mpr ⟨h_31, (by
                      let _atomic_wd_2_1 := (Litex.intersect _value_i2 _value_i3)
                      exact ((Litex.inIntersect_iff _value_i4 _value_i2 _value_i3).mpr ⟨h_32, h_22⟩))⟩))
                )
            )

          have h_259 : Litex.In _value_i4 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff _value_i4 _value_i1 (Litex.intersect _value_i2 _value_i3)).mp h_4).1)
                )
            )

          have h_260 : Litex.In _value_i4 (Litex.intersect _value_i2 _value_i3) :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff _value_i4 _value_i1 (Litex.intersect _value_i2 _value_i3)).mp h_4).2)
                )
            )
          exact (by
            let _atomic_wd_1_1 := _object_w5
            exact h_4)
        )
      )
  )

theorem h_301 : (by
  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.R (M := M));
  let _wd_1_1 := (Litex.intersect (Litex.C (M := M)) (Litex.C (M := M)));
  (Litex.intersect _wd_1_0 _wd_1_1))
  exact Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_302 : Litex.IsSet (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.isSet (Litex.R (M := M)))
                )
            )
          have h_303 : Litex.IsSet (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.isSet (Litex.C (M := M)))
                )
            )
          have h_304 : Litex.IsSet (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_303
                )
            )
          have h_305 : (by
            let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.intersect (Litex.R (M := M)) (Litex.C (M := M)));
            let _wd_1_1 := (Litex.C (M := M));
            (Litex.intersect _wd_1_0 _wd_1_1))
            exact Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.intersect (Litex.R (M := M)) (Litex.C (M := M)));
                    let _wd_1_1 := (Litex.C (M := M));
                    (Litex.intersect _wd_1_0 _wd_1_1))
                    exact ((Litex.inIntersect_iff (Litex.number (M := M) (1 : ℂ)) (Litex.intersect (Litex.R (M := M)) (Litex.C (M := M))) (Litex.C (M := M))).mpr ⟨(by
                      let _atomic_wd_2_1 := (Litex.intersect (Litex.R (M := M)) (Litex.C (M := M)))
                      exact ((Litex.inIntersect_iff (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) (Litex.C (M := M))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), (Litex.numberInC (M := M) (1 : ℂ))⟩)), (Litex.numberInC (M := M) (1 : ℂ))⟩))
                )
            )
          have h_320 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.intersect (Litex.R (M := M)) (Litex.C (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff (Litex.number (M := M) (1 : ℂ)) (Litex.intersect (Litex.R (M := M)) (Litex.C (M := M))) (Litex.C (M := M))).mp h_305).1)
                )
            )
          have h_321 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff (Litex.number (M := M) (1 : ℂ)) (Litex.intersect (Litex.R (M := M)) (Litex.C (M := M))) (Litex.C (M := M))).mp h_305).2)
                )
            )
          have h_306 : Litex.In (Litex.number (M := M) (1 : ℂ)) (let _wd_1_0 := (Litex.R (M := M));
          let _wd_1_1 := (Litex.intersect (Litex.C (M := M)) (Litex.C (M := M)));
          (Litex.intersect _wd_1_0 _wd_1_1)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2 (M := M)) (Litex.R (M := M)) h_302 (Litex.C (M := M)) h_303 (Litex.C (M := M)) h_304 (Litex.number (M := M) (1 : ℂ)) h_305)
                )
            )
          have h_328 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) (Litex.intersect (Litex.C (M := M)) (Litex.C (M := M)))).mp h_306).1)
                )
            )
          have h_329 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.intersect (Litex.C (M := M)) (Litex.C (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) (Litex.intersect (Litex.C (M := M)) (Litex.C (M := M)))).mp h_306).2)
                )
            )
          exact (by
          let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.R (M := M));
          let _wd_1_1 := (Litex.intersect (Litex.C (M := M)) (Litex.C (M := M)));
          (Litex.intersect _wd_1_0 _wd_1_1))
          exact h_306)
        )
      )
  )

theorem h_338 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (((Litex.inIntersect_iff (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) (Litex.intersect (Litex.C (M := M)) (Litex.C (M := M)))).mp (h_301 (M := M))).1)
      )
  )

theorem h_339 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.intersect (Litex.C (M := M)) (Litex.C (M := M))) :=
  (by
    litex_complete =>
      exact (
        (((Litex.inIntersect_iff (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) (Litex.intersect (Litex.C (M := M)) (Litex.C (M := M)))).mp (h_301 (M := M))).2)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_intersection_x5f_reassociation_x2f_statement_x2e_lit
