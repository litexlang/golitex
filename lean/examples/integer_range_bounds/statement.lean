import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_range_x5f_bounds_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_45 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.range _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))), ((Litex.In _value_i1 (Litex.Z (M := M))) ∧ ((((by
  let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
  exact Litex.Le _atomic_wd_1_0 _value_i1)) ∧ (Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_45
          have h_46 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_45).1
                )
            )
          have h_47 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_45).2.1
                )
            )
          have h_48 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) _value_i1 h_45).2.2
                )
            )
          have h_1 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_46
                )
            )
          have h_2 : (by
            let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
            exact Litex.Le _atomic_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                    exact h_47)
                )
            )
          have h_3 : Litex.Lt _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_48
                )
            )
          exact (And.intro h_1 (And.intro h_2 h_3))
        )
      )
  )

theorem h_169 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_197 : Litex.In _value_i2 (Litex.Z (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_198 : Litex.In _value_i3 (Litex.Z (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_211 : Litex.In _value_i4 (Litex.range _value_i2 _value_i3 h_197 h_198)), ((Litex.Le _value_i2 _value_i4) ∧ (Litex.Lt _value_i4 _value_i3)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_197 _Host_i3 _rep_i3 _value_i3 h_198 _Host_i4 _rep_i4 _value_i4 h_211
          have h_212 : Litex.In _value_i4 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range _value_i2 _value_i3 h_197 h_198) _value_i4 h_211).1
                )
            )
          have h_213 : Litex.Le _value_i2 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range _value_i2 _value_i3 h_197 h_198) _value_i4 h_211).2.1
                )
            )
          have h_214 : Litex.Lt _value_i4 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range _value_i2 _value_i3 h_197 h_198) _value_i4 h_211).2.2
                )
            )
          have h_167 : Litex.Le _value_i2 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  h_213
                )
            )
          have h_168 : Litex.Lt _value_i4 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  h_214
                )
            )
          exact (And.intro h_167 h_168)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_range_x5f_bounds_x2f_statement_x2e_lit
