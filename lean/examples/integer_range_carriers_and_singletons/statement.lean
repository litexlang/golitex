import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_range_x5f_carriers_x5f_and_x5f_singletons_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_29 : Litex.In _value_i1 (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)))), Litex.In _value_i1 (Litex.NPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_29
          have h_30 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num))) _value_i1 h_29).1
                )
            )
          have h_31 : Litex.Le (Litex.number (M := M) (2 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num))) _value_i1 h_29).2.1
                )
            )
          have h_32 : Litex.Lt _value_i1 (Litex.number (M := M) (5 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num))) _value_i1 h_29).2.2
                )
            )
          have h_33 : Litex.In _value_i1 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangePositive (Litex.range (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num))) _value_i1 (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) (by norm_num) h_29)
                )
            )
          have h_1 : Litex.In _value_i1 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_33
                )
            )
          have h_46 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i1 h_1)
                )
            )
          have h_47 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_46)
                )
            )
          have h_48 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_46) _litex_zero.symm)
                )
            )
          exact h_1
        )
      )
  )

theorem h_50 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_105 : Litex.In _value_i2 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
let _wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
(Litex.range _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num))))))), (by
  let _equal_wd_1_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
  exact Litex.Same _value_i2 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_105
          have h_106 : Litex.In _value_i2 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  let _wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))))) _value_i2 h_105).1
                )
            )
          have h_107 : Litex.Le (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  let _wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))))) _value_i2 h_105).2.1
                )
            )
          have h_108 : Litex.Lt _value_i2 (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  let _wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))))) _value_i2 h_105).2.2
                )
            )
          have h_109 : Litex.Same _value_i2 (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    obtain ⟨k, hk, hlo, hhi⟩ := Litex.inRangeInteger (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
                  let _wd_1_1 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  (Litex.range _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num)))) (by
                    let _atomic_wd_1_0 := _wd_1_1
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))))) _value_i2 (-2 : ℤ) (-1 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = ((-2 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = ((-1 : ℤ) : ℂ)))) h_105
                    have heq : k = (-2 : ℤ) := by omega
                    exact hk.trans ((congrArg M.number (by norm_num [heq] : (k : ℂ) = (- (2 : ℂ)))).trans ((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).symm)
                  )
                )
            )
          have h_49 : (by
            let _equal_wd_1_1 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))
            exact Litex.Same _value_i2 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_109
                )
            )
          exact h_49
        )
      )
  )

theorem h_112 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_139 : Litex.In _value_i3 (Litex.closedRange (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), Litex.Same _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_139
          have h_140 : Litex.In _value_i3 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_139).1
                )
            )
          have h_141 : Litex.Le (Litex.number (M := M) (2 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_139).2.1
                )
            )
          have h_142 : Litex.Le _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 h_139).2.2
                )
            )
          have h_143 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) (by norm_num) h_139)
                )
            )
          have h_144 : Litex.Same _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    obtain ⟨k, hk, hlo, hhi⟩ := Litex.inClosedRangeInteger (Litex.closedRange (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i3 (2 : ℤ) (2 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = ((2 : ℤ) : ℂ)))) h_139
                    have heq : k = (2 : ℤ) := by omega
                    exact hk.trans ((congrArg M.number (by norm_num [heq] : (k : ℂ) = (2 : ℂ))).trans ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).symm)
                  )
                )
            )
          have h_111 : Litex.Same _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_144
                )
            )
          exact h_111
        )
      )
  )

noncomputable def _object_w15 := (Litex.range (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)))

theorem h_146 : (by
  let _atomic_wd_1_0 := (_object_w15 (M := M))
  exact Litex.IsSet _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w15 (M := M))
          exact (Litex.isSet _atomic_wd_1_0))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_range_x5f_carriers_x5f_and_x5f_singletons_x2f_statement_x2e_lit
