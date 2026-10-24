import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_expand_x5f_closed_x5f_integer_x5f_range_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_10 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
(Litex.closedRange _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))), ((Litex.Same _value_i1 (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))) ∨ (((Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_10
          have h_11 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_10).1
                )
            )
          have h_12 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_10).2.1
                )
            )
          have h_13 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_10).2.2
                )
            )
          have h_18 : Litex.In _value_i1 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.closedRange _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_19 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_18).1
                )
            )
          have h_20 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_18).2.1
                )
            )
          have h_21 : Litex.Le _value_i1 (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i1 h_18).2.2
                )
            )
          have h_30 : (Litex.Same _value_i1 (Litex.number (M := M) (-1 : ℂ))) ∨ (Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _expanded_range := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))
                    obtain ⟨_range_integer, _range_same, _range_lower, _range_upper⟩ := Litex.inClosedRangeInteger _expanded_range _value_i1 (-1 : ℤ) (1 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = ((-1 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by
                      let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                      (Litex.closedRange _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))
                      exact h_18)
                    have _range_cases : _range_integer = (-1 : ℤ) ∨ _range_integer = (0 : ℤ) ∨ _range_integer = (1 : ℤ) := by omega
                    rcases _range_cases with _range_case | _range_case | _range_case
                    · exact (Or.inl (_range_same.trans (congrArg M.number (by norm_num [_range_case]))))
                    · exact (Or.inr (Or.inl (_range_same.trans (congrArg M.number (by norm_num [_range_case])))))
                    · exact (Or.inr (Or.inr (_range_same.trans (congrArg M.number (by norm_num [_range_case])))))
                  )
                )
            )
          exact ((fun _known_tail => Or.elim _known_tail (fun _known_or_0 => Or.inl (Eq.trans (Eq.symm (show @Eq M.Value _ _ from Eq.refl _)) (Eq.trans _known_or_0 ((congrArg M.number (by norm_num : (-1 : ℂ) = (- (1 : ℂ)))).trans ((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).symm)))) (fun _known_rest => Or.inr ((fun _known_tail => Or.elim _known_tail (fun _known_or_1 => Or.inl (Eq.trans (Eq.symm (show @Eq M.Value _ _ from Eq.refl _)) (Eq.trans _known_or_1 (show @Eq M.Value _ _ from Eq.refl _)))) (fun _known_rest => Or.inr ((fun _known_or_2 => (Eq.trans (Eq.symm (show @Eq M.Value _ _ from Eq.refl _)) (Eq.trans _known_or_2 (show @Eq M.Value _ _ from Eq.refl _)))) _known_rest))) _known_rest))) h_30)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_expand_x5f_closed_x5f_integer_x5f_range_x2f_statement_x2e_lit
