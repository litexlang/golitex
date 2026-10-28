import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_integer_x5f_row_x5f_cases_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_32 : Litex.In _value_i1 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))), ((Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))) ∨ (((Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ))) ∨ (Litex.Same _value_i1 (Litex.number (M := M) (3 : ℂ)))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_32
          have h_33 : Litex.In _value_i1 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_32).1
                )
            )
          have h_34 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_32).2.1
                )
            )
          have h_35 : Litex.Le _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_32).2.2
                )
            )
          have h_36 : Litex.In _value_i1 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_32)
                )
            )
          have h_4 : ((Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))) ∨ (((Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ))) ∨ (Litex.Same _value_i1 (Litex.number (M := M) (3 : ℂ)))))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _interval := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                    have _member : (by
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) := (by
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
                      exact h_32)
                    have _carrier : Litex.Same (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _interval := (show @Eq M.Value _ _ from Eq.refl _)
                    have _range_member : Litex.In _value_i1 _interval := by change M.mem (Litex.denote _value_i1) (Litex.denote _interval); rw [← _carrier]; exact _member
                    obtain ⟨_lower, _upper, _k, _hl, _hu, _hx, _hlo, _hhi⟩ := (Litex.inClosedRange_iff _interval.val.start _interval.val.finish _value_i1 _interval.wd.1 _interval.wd.2).mp _range_member
                    have _start_num : Litex.denote _interval.val.start = M.number ((1 : ℤ) : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))
                    have _lo : _lower = (1 : ℤ) := by exact_mod_cast M.number_injective (_hl.symm.trans _start_num)
                    have _end_num : Litex.denote _interval.val.finish = M.number ((3 : ℤ) : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))
                    have _hi : _upper = (3 : ℤ) := by exact_mod_cast M.number_injective (_hu.symm.trans _end_num)
                    subst _lower _upper
                    have _cases : _k = (1 : ℤ) ∨ _k = (2 : ℤ) ∨ _k = (3 : ℤ) := by omega
                    rcases _cases with _case_0 | _case_1 | _case_2
                    · exact Or.inl ((show Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_0)).trans ((show Litex.denote (Litex.number (M := M) (1 : ℂ)) = M.number ((1 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num)))).symm)))
                    · exact Or.inr (Or.inl ((show Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_1)).trans ((show Litex.denote (Litex.number (M := M) (2 : ℂ)) = M.number ((2 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num)))).symm))))
                    · exact Or.inr (Or.inr ((show Litex.Same _value_i1 (Litex.number (M := M) (3 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_2)).trans ((show Litex.denote (Litex.number (M := M) (3 : ℂ)) = M.number ((3 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num)))).symm))))
                  )
                )
            )
          exact h_4
        )
      )
  )

theorem h_47 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_74 : Litex.In _value_i2 (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)))), ((Litex.Same (Litex.number (M := M) (3 : ℂ)) _value_i2) ∨ (((Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ))) ∨ (((Litex.Same (Litex.number (M := M) (2 : ℂ)) _value_i2) ∨ (((Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)))))))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_74
          have h_75 : Litex.In _value_i2 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_74).1
                )
            )
          have h_76 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_74).2.1
                )
            )
          have h_77 : Litex.Lt _value_i2 (Litex.number (M := M) (4 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangeBounds (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 h_74).2.2
                )
            )
          have h_78 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRangePositive (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_74)
                )
            )
          have h_46 : ((Litex.Same (Litex.number (M := M) (3 : ℂ)) _value_i2) ∨ (((Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ))) ∨ (((Litex.Same (Litex.number (M := M) (2 : ℂ)) _value_i2) ∨ (((Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)))))))))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _interval := (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)))
                    have _member : (by
                      let _atomic_wd_1_1 := (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)))
                      exact Litex.In _value_i2 _atomic_wd_1_1) := (by
                      let _atomic_wd_1_1 := (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)))
                      exact h_74)
                    have _carrier : Litex.Same (Litex.range (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num))) _interval := (show @Eq M.Value _ _ from Eq.refl _)
                    have _range_member : Litex.In _value_i2 _interval := by change M.mem (Litex.denote _value_i2) (Litex.denote _interval); rw [← _carrier]; exact _member
                    obtain ⟨_lower, _upper, _k, _hl, _hu, _hx, _hlo, _hhi⟩ := (Litex.inRange_iff _interval.val.start _interval.val.finish _value_i2 _interval.wd.1 _interval.wd.2).mp _range_member
                    have _start_num : Litex.denote _interval.val.start = M.number ((1 : ℤ) : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))
                    have _lo : _lower = (1 : ℤ) := by exact_mod_cast M.number_injective (_hl.symm.trans _start_num)
                    have _end_num : Litex.denote _interval.val.finish = M.number ((4 : ℤ) : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))
                    have _hi : _upper = (4 : ℤ) := by exact_mod_cast M.number_injective (_hu.symm.trans _end_num)
                    subst _lower _upper
                    have _cases : _k = (1 : ℤ) ∨ _k = (2 : ℤ) ∨ _k = (3 : ℤ) := by omega
                    rcases _cases with _case_0 | _case_1 | _case_2
                    · exact Or.inr (Or.inl ((show Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_0)).trans ((show Litex.denote (Litex.number (M := M) (1 : ℂ)) = M.number ((1 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num)))).symm))))
                    · exact Or.inr (Or.inr (Or.inl (((show Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_1)).trans ((show Litex.denote (Litex.number (M := M) (2 : ℂ)) = M.number ((2 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num)))).symm))).symm)))
                    · exact Or.inl (((show Litex.Same _value_i2 (Litex.number (M := M) (3 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_2)).trans ((show Litex.denote (Litex.number (M := M) (3 : ℂ)) = M.number ((3 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num)))).symm))).symm)
                  )
                )
            )
          exact h_46
        )
      )
  )

theorem h_87 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_128 : Litex.In _value_i3 (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
(Litex.closedRange _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))), ((Litex.Same _value_i3 (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))) ∨ (((Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_128
          have h_129 : Litex.In _value_i3 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i3 h_128).1
                )
            )
          have h_130 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i3 h_128).2.1
                )
            )
          have h_131 : Litex.Le _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.closedRange _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _value_i3 h_128).2.2
                )
            )
          have h_86 : ((Litex.Same _value_i3 (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))) ∨ (((Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))) ∨ (Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)))))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _interval := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))
                    have _member : (by
                      let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                      (Litex.closedRange _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))
                      exact Litex.In _value_i3 _atomic_wd_1_1) := (by
                      let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                      let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                      (Litex.closedRange _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := _wd_1_0
                        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))
                      exact h_128)
                    have _carrier : Litex.Same (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
                    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.closedRange _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (1 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (1 : ℂ)) (-1 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) _interval := (show @Eq M.Value _ _ from Eq.refl _)
                    have _range_member : Litex.In _value_i3 _interval := by change M.mem (Litex.denote _value_i3) (Litex.denote _interval); rw [← _carrier]; exact _member
                    obtain ⟨_lower, _upper, _k, _hl, _hu, _hx, _hlo, _hhi⟩ := (Litex.inClosedRange_iff _interval.val.start _interval.val.finish _value_i3 _interval.wd.1 _interval.wd.2).mp _range_member
                    have _start_num : Litex.denote _interval.val.start = M.number ((-1 : ℤ) : ℂ) := ((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))
                    have _lo : _lower = (-1 : ℤ) := by exact_mod_cast M.number_injective (_hl.symm.trans _start_num)
                    have _end_num : Litex.denote _interval.val.finish = M.number ((1 : ℤ) : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))
                    have _hi : _upper = (1 : ℤ) := by exact_mod_cast M.number_injective (_hu.symm.trans _end_num)
                    subst _lower _upper
                    have _cases : _k = (-1 : ℤ) ∨ _k = (0 : ℤ) ∨ _k = (1 : ℤ) := by omega
                    rcases _cases with _case_0 | _case_1 | _case_2
                    · exact Or.inl ((show Litex.Same _value_i3 (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_0)).trans ((show Litex.denote (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) = M.number ((-1 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num)))).symm)))
                    · exact Or.inr (Or.inl ((show Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_1)).trans ((show Litex.denote (Litex.number (M := M) (0 : ℂ)) = M.number ((0 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num)))).symm))))
                    · exact Or.inr (Or.inr ((show Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_2)).trans ((show Litex.denote (Litex.number (M := M) (1 : ℂ)) = M.number ((1 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num)))).symm))))
                  )
                )
            )
          exact h_86
        )
      )
  )

noncomputable def _object_i4 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
theorem h_142 : Litex.IsSet (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
          exact (Litex.isSet _atomic_wd_1_0))
      )
  )
theorem h_143 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))))
      )
  )

theorem h_148 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_161 : Litex.In _value_i5 (_object_i4 (M := M))), ((Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ))) ∨ (((Litex.Same _value_i5 (Litex.number (M := M) (2 : ℂ))) ∨ (Litex.Same _value_i5 (Litex.number (M := M) (3 : ℂ)))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_161
          have h_147 : ((Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ))) ∨ (((Litex.Same _value_i5 (Litex.number (M := M) (2 : ℂ))) ∨ (Litex.Same _value_i5 (Litex.number (M := M) (3 : ℂ)))))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _interval := (_object_i4 (M := M))
                    have _member : Litex.In _value_i5 (_object_i4 (M := M)) := h_161
                    have _carrier : Litex.Same (_object_i4 (M := M)) _interval := (h_143 (M := M))
                    have _range_member : Litex.In _value_i5 _interval := by change M.mem (Litex.denote _value_i5) (Litex.denote _interval); rw [← _carrier]; exact _member
                    obtain ⟨_lower, _upper, _k, _hl, _hu, _hx, _hlo, _hhi⟩ := (Litex.inClosedRange_iff _interval.val.start _interval.val.finish _value_i5 _interval.wd.1 _interval.wd.2).mp _range_member
                    have _start_num : Litex.denote _interval.val.start = M.number ((1 : ℤ) : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))
                    have _lo : _lower = (1 : ℤ) := by exact_mod_cast M.number_injective (_hl.symm.trans _start_num)
                    have _end_num : Litex.denote _interval.val.finish = M.number ((3 : ℤ) : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))
                    have _hi : _upper = (3 : ℤ) := by exact_mod_cast M.number_injective (_hu.symm.trans _end_num)
                    subst _lower _upper
                    have _cases : _k = (1 : ℤ) ∨ _k = (2 : ℤ) ∨ _k = (3 : ℤ) := by omega
                    rcases _cases with _case_0 | _case_1 | _case_2
                    · exact Or.inl ((show Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_0)).trans ((show Litex.denote (Litex.number (M := M) (1 : ℂ)) = M.number ((1 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num)))).symm)))
                    · exact Or.inr (Or.inl ((show Litex.Same _value_i5 (Litex.number (M := M) (2 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_1)).trans ((show Litex.denote (Litex.number (M := M) (2 : ℂ)) = M.number ((2 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num)))).symm))))
                    · exact Or.inr (Or.inr ((show Litex.Same _value_i5 (Litex.number (M := M) (3 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_2)).trans ((show Litex.denote (Litex.number (M := M) (3 : ℂ)) = M.number ((3 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num)))).symm))))
                  )
                )
            )
          exact h_147
        )
      )
  )

noncomputable def _object_i6 := (show Litex.Obj (M := M) (Litex.PiecewiseFn M) from by
  let _signature := ((show Litex.Obj (M := M) (Litex.FunctionSignature M) from (let _checked_header : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote (_object_i4 (M := M))) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → True := (by
      intro _raw_i7 h_169 _
      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_169)
      have h_169 : Litex.In _value_i7 (_object_i4 (M := M)) := h_169
      have h_170 : Litex.In _value_i7 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_169).1
            )
        )
      have h_171 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_169).2.1
            )
        )
      have h_172 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_169).2.2
            )
        )
      have h_173 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_169)
            )
        )
      exact True.intro);
    Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.denote _litex_output) (Litex.isSet (_object_i4 (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input))))).val
  let _branch_0 := (⟨(fun (_input : M.Value) => (_input = (M.number (1 : ℂ)))), (fun (_input : M.Value) => (M.number (10 : ℂ)))⟩ : Litex.FunctionBranch M)
  let _branch_1 := (⟨(fun (_input : M.Value) => (_input = (M.number (2 : ℂ)))), (fun (_input : M.Value) => (M.number (20 : ℂ)))⟩ : Litex.FunctionBranch M)
  let _branch_2 := (⟨(fun (_input : M.Value) => (_input = (M.number (3 : ℂ)))), (fun (_input : M.Value) => (M.number (30 : ℂ)))⟩ : Litex.FunctionBranch M)
  have _coverage : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote (_object_i4 (M := M))) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → (((_raw_i7 = (M.number (1 : ℂ)))) ∨ ((((_raw_i7 = (M.number (2 : ℂ)))) ∨ ((_raw_i7 = (M.number (3 : ℂ))))))) := (by
    intro _raw_i7 h_174 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_174)
    have h_174 : Litex.In _value_i7 (_object_i4 (M := M)) := h_174
    have h_175 : Litex.In _value_i7 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).1
          )
      )
    have h_176 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.1
          )
      )
    have h_177 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.2
          )
      )
    have h_178 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_174)
          )
      )
    exact (by
      let _interval := (_object_i4 (M := M))
      have _member : (by
        let _atomic_wd_1_1 := (_object_i4 (M := M))
        exact Litex.In _value_i7 _atomic_wd_1_1) := (by
        let _atomic_wd_1_1 := (_object_i4 (M := M))
        exact h_174)
      have _carrier : Litex.Same (_object_i4 (M := M)) _interval := (show @Eq M.Value _ _ from Eq.refl _)
      have _range_member : Litex.In _value_i7 _interval := by change M.mem (Litex.denote _value_i7) (Litex.denote _interval); rw [← _carrier]; exact _member
      obtain ⟨_lower, _upper, _k, _hl, _hu, _hx, _hlo, _hhi⟩ := (Litex.inClosedRange_iff _interval.val.start _interval.val.finish _value_i7 _interval.wd.1 _interval.wd.2).mp _range_member
      have _start_num : Litex.denote _interval.val.start = M.number ((1 : ℤ) : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))
      have _lo : _lower = (1 : ℤ) := by exact_mod_cast M.number_injective (_hl.symm.trans _start_num)
      have _end_num : Litex.denote _interval.val.finish = M.number ((3 : ℤ) : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))
      have _hi : _upper = (3 : ℤ) := by exact_mod_cast M.number_injective (_hu.symm.trans _end_num)
      subst _lower _upper
      have _cases : _k = (1 : ℤ) ∨ _k = (2 : ℤ) ∨ _k = (3 : ℤ) := by omega
      rcases _cases with _case_0 | _case_1 | _case_2
      · exact Or.inl ((show Litex.Same _value_i7 (Litex.number (M := M) (1 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_0)).trans ((show Litex.denote (Litex.number (M := M) (1 : ℂ)) = M.number ((1 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num)))).symm)))
      · exact Or.inr (Or.inl ((show Litex.Same _value_i7 (Litex.number (M := M) (2 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_1)).trans ((show Litex.denote (Litex.number (M := M) (2 : ℂ)) = M.number ((2 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num)))).symm))))
      · exact Or.inr (Or.inr ((show Litex.Same _value_i7 (Litex.number (M := M) (3 : ℂ)) from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_2)).trans ((show Litex.denote (Litex.number (M := M) (3 : ℂ)) = M.number ((3 : ℤ) : ℂ) from ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num)))).symm))))
    ))
  have _apart_0_1 : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote (_object_i4 (M := M))) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → ((_raw_i7 = (M.number (1 : ℂ)))) → ((_raw_i7 = (M.number (2 : ℂ)))) → False := (by
    intro _raw_i7 h_174 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_174)
    have h_174 : Litex.In _value_i7 (_object_i4 (M := M)) := h_174
    have h_175 : Litex.In _value_i7 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).1
          )
      )
    have h_176 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.1
          )
      )
    have h_177 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.2
          )
      )
    have h_178 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_174)
          )
      )
    have h_184 := h_174
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_184)
    have h_184 : Litex.In _value_i7 (_object_i4 (M := M)) := h_184
    have h_185 : Litex.In _value_i7 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_184).1
          )
      )
    have h_186 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_184).2.1
          )
      )
    have h_187 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_184).2.2
          )
      )
    have h_188 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_184)
          )
      )
    intro h_166 _other
    have h_166 : (_raw_i7 = (M.number (1 : ℂ))) := h_166
    have _excluded : ¬ Litex.Same _value_i7 (Litex.number (M := M) (2 : ℂ)) := (Litex.notSameOfSame (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (h_166).symm (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)))
    exact (_excluded _other))
  have _apart_0_2 : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote (_object_i4 (M := M))) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → ((_raw_i7 = (M.number (1 : ℂ)))) → ((_raw_i7 = (M.number (3 : ℂ)))) → False := (by
    intro _raw_i7 h_174 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_174)
    have h_174 : Litex.In _value_i7 (_object_i4 (M := M)) := h_174
    have h_175 : Litex.In _value_i7 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).1
          )
      )
    have h_176 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.1
          )
      )
    have h_177 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.2
          )
      )
    have h_178 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_174)
          )
      )
    have h_228 := h_174
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_228)
    have h_228 : Litex.In _value_i7 (_object_i4 (M := M)) := h_228
    have h_229 : Litex.In _value_i7 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_228).1
          )
      )
    have h_230 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_228).2.1
          )
      )
    have h_231 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_228).2.2
          )
      )
    have h_232 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_228)
          )
      )
    intro h_166 _other
    have h_166 : (_raw_i7 = (M.number (1 : ℂ))) := h_166
    have _excluded : ¬ Litex.Same _value_i7 (Litex.number (M := M) (3 : ℂ)) := (Litex.notSameOfSame (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_166).symm (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)))
    exact (_excluded _other))
  have _apart_1_2 : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote (_object_i4 (M := M))) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → ((_raw_i7 = (M.number (2 : ℂ)))) → ((_raw_i7 = (M.number (3 : ℂ)))) → False := (by
    intro _raw_i7 h_174 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_174)
    have h_174 : Litex.In _value_i7 (_object_i4 (M := M)) := h_174
    have h_175 : Litex.In _value_i7 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).1
          )
      )
    have h_176 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.1
          )
      )
    have h_177 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.2
          )
      )
    have h_178 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_174)
          )
      )
    have h_272 := h_174
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_272)
    have h_272 : Litex.In _value_i7 (_object_i4 (M := M)) := h_272
    have h_273 : Litex.In _value_i7 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_272).1
          )
      )
    have h_274 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_272).2.1
          )
      )
    have h_275 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_272).2.2
          )
      )
    have h_276 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_272)
          )
      )
    intro h_167 _other
    have h_167 : (_raw_i7 = (M.number (2 : ℂ))) := h_167
    have _excluded : ¬ Litex.Same _value_i7 (Litex.number (M := M) (3 : ℂ)) := (Litex.notSameOfSame (Litex.number (M := M) (2 : ℂ)) _value_i7 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_167).symm (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)))
    exact (_excluded _other))
  have _return_0 : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote (_object_i4 (M := M))) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → ((_raw_i7 = (M.number (1 : ℂ)))) → ((M.mem (M.number (10 : ℂ)) (M.standard Litex.StandardSetValue.real))) := (by
    intro _raw_i7 h_174 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_174)
    have h_174 : Litex.In _value_i7 (_object_i4 (M := M)) := h_174
    have h_175 : Litex.In _value_i7 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).1
          )
      )
    have h_176 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.1
          )
      )
    have h_177 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.2
          )
      )
    have h_178 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_174)
          )
      )
    have h_316 := h_174
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_316)
    have h_316 : Litex.In _value_i7 (_object_i4 (M := M)) := h_316
    have h_317 : Litex.In _value_i7 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_316).1
          )
      )
    have h_318 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_316).2.1
          )
      )
    have h_319 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_316).2.2
          )
      )
    have h_320 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_316)
          )
      )
    intro h_166
    have h_166 : (_raw_i7 = (M.number (1 : ℂ))) := h_166
    have _formed_body := (Litex.number (M := M) (10 : ℂ))
    exact (Litex.NativeBridge.numberInROfEq (M := M) (10 : ℂ) (10 : ℝ) (by norm_num)))
  have _return_1 : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote (_object_i4 (M := M))) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → ((_raw_i7 = (M.number (2 : ℂ)))) → ((M.mem (M.number (20 : ℂ)) (M.standard Litex.StandardSetValue.real))) := (by
    intro _raw_i7 h_174 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_174)
    have h_174 : Litex.In _value_i7 (_object_i4 (M := M)) := h_174
    have h_175 : Litex.In _value_i7 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).1
          )
      )
    have h_176 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.1
          )
      )
    have h_177 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.2
          )
      )
    have h_178 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_174)
          )
      )
    have h_328 := h_174
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_328)
    have h_328 : Litex.In _value_i7 (_object_i4 (M := M)) := h_328
    have h_329 : Litex.In _value_i7 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_328).1
          )
      )
    have h_330 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_328).2.1
          )
      )
    have h_331 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_328).2.2
          )
      )
    have h_332 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_328)
          )
      )
    intro h_167
    have h_167 : (_raw_i7 = (M.number (2 : ℂ))) := h_167
    have _formed_body := (Litex.number (M := M) (20 : ℂ))
    exact (Litex.NativeBridge.numberInROfEq (M := M) (20 : ℂ) (20 : ℝ) (by norm_num)))
  have _return_2 : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote (_object_i4 (M := M))) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → ((_raw_i7 = (M.number (3 : ℂ)))) → ((M.mem (M.number (30 : ℂ)) (M.standard Litex.StandardSetValue.real))) := (by
    intro _raw_i7 h_174 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_174)
    have h_174 : Litex.In _value_i7 (_object_i4 (M := M)) := h_174
    have h_175 : Litex.In _value_i7 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).1
          )
      )
    have h_176 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.1
          )
      )
    have h_177 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_174).2.2
          )
      )
    have h_178 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_174)
          )
      )
    have h_340 := h_174
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_340)
    have h_340 : Litex.In _value_i7 (_object_i4 (M := M)) := h_340
    have h_341 : Litex.In _value_i7 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_340).1
          )
      )
    have h_342 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_340).2.1
          )
      )
    have h_343 : Litex.Le _value_i7 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (_object_i4 (M := M)) _value_i7 h_340).2.2
          )
      )
    have h_344 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (_object_i4 (M := M)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_340)
          )
      )
    intro h_168
    have h_168 : (_raw_i7 = (M.number (3 : ℂ))) := h_168
    have _formed_body := (Litex.number (M := M) (30 : ℂ))
    exact (Litex.NativeBridge.numberInROfEq (M := M) (30 : ℂ) (30 : ℝ) (by norm_num)))
  apply Litex.piecewiseFn _signature [_branch_0, _branch_1, _branch_2]
  refine ⟨?_, ?_, ?_⟩
  · intro _input _input_member
    obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (_object_i4 (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (_object_i4 (M := M))) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _input).mp _input_member
    rcases _coverage _input _members _domain with _case | _case | _case
    · exact ⟨_branch_0, (List.mem_cons_self), _case⟩
    · exact ⟨_branch_1, (List.mem_cons_of_mem _ (List.mem_cons_self)), _case⟩
    · exact ⟨_branch_2, (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))), _case⟩
  · exact (List.Pairwise.cons (by
    intro _branch _member
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (_object_i4 (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (_object_i4 (M := M))) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _input).mp _input_member
      rintro ⟨_left, _right⟩
      exact _apart_0_1 _input _members _domain _left _right)
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (_object_i4 (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (_object_i4 (M := M))) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _input).mp _input_member
      rintro ⟨_left, _right⟩
      exact _apart_0_2 _input _members _domain _left _right)
    cases _member) (List.Pairwise.cons (by
    intro _branch _member
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (_object_i4 (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (_object_i4 (M := M))) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _input).mp _input_member
      rintro ⟨_left, _right⟩
      exact _apart_1_2 _input _members _domain _left _right)
    cases _member) (List.Pairwise.cons (by
    intro _branch _member
    cases _member) List.Pairwise.nil)))
  · exact (by
    intro _branch _member
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member _case
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (_object_i4 (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (_object_i4 (M := M))) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _input).mp _input_member
      exact _return_0 _input _members _domain _case)
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member _case
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (_object_i4 (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (_object_i4 (M := M))) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _input).mp _input_member
      exact _return_1 _input _members _domain _case)
    rcases List.mem_cons.mp _member with rfl | _member
    · exact (by
      intro _input _input_member _case
      obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (_object_i4 (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (_object_i4 (M := M))) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _input).mp _input_member
      exact _return_2 _input _members _domain _case)
    cases _member))

theorem h_352 : Litex.In (_object_i6 (M := M)) (Litex.fnSet ((_object_i6 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.piecewiseFnInFnSet (_object_i6 (M := M)))
      )
  )

theorem h_354 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_316 : M.mem (Litex.denote _value_i7) (Litex.denote (_object_i4 (M := M)))) (h_166 : ((Litex.denote _value_i7) = (M.number (1 : ℂ)))), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.denote _value_i7)) = (M.number (10 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_316 h_166
          have _case_domain : M.mem (Litex.denote _value_i7) ((_object_i6 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (Litex.denote (_object_i4 (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (_object_i4 (M := M))) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) (Litex.denote _value_i7)).mpr ⟨h_316, (Eq.mpr rfl (True.intro : (fun (_raw_i7 : M.Value) => True) (Litex.denote _value_i7)))⟩
          exact (Litex.piecewiseFn_call_eq (_object_i6 (M := M)) (⟨(fun (_input : M.Value) => (fun (_raw_i7 : M.Value) => (_raw_i7 = (M.number (1 : ℂ)))) _input), (fun (_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.number (10 : ℂ))) _input)⟩ : Litex.FunctionBranch M) (List.mem_cons_self) (Litex.denote _value_i7) _case_domain (Eq.mpr rfl (h_166 : (fun (_raw_i7 : M.Value) => (_raw_i7 = (M.number (1 : ℂ)))) (Litex.denote _value_i7)))).trans rfl)
      )
  )

theorem h_356 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_328 : M.mem (Litex.denote _value_i7) (Litex.denote (_object_i4 (M := M)))) (h_167 : ((Litex.denote _value_i7) = (M.number (2 : ℂ)))), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.denote _value_i7)) = (M.number (20 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_328 h_167
          have _case_domain : M.mem (Litex.denote _value_i7) ((_object_i6 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (Litex.denote (_object_i4 (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (_object_i4 (M := M))) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) (Litex.denote _value_i7)).mpr ⟨h_328, (Eq.mpr rfl (True.intro : (fun (_raw_i7 : M.Value) => True) (Litex.denote _value_i7)))⟩
          exact (Litex.piecewiseFn_call_eq (_object_i6 (M := M)) (⟨(fun (_input : M.Value) => (fun (_raw_i7 : M.Value) => (_raw_i7 = (M.number (2 : ℂ)))) _input), (fun (_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.number (20 : ℂ))) _input)⟩ : Litex.FunctionBranch M) (List.mem_cons_of_mem _ (List.mem_cons_self)) (Litex.denote _value_i7) _case_domain (Eq.mpr rfl (h_167 : (fun (_raw_i7 : M.Value) => (_raw_i7 = (M.number (2 : ℂ)))) (Litex.denote _value_i7)))).trans rfl)
      )
  )

theorem h_358 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_340 : M.mem (Litex.denote _value_i7) (Litex.denote (_object_i4 (M := M)))) (h_168 : ((Litex.denote _value_i7) = (M.number (3 : ℂ)))), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.denote _value_i7)) = (M.number (30 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_340 h_168
          have _case_domain : M.mem (Litex.denote _value_i7) ((_object_i6 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (Litex.denote (_object_i4 (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (_object_i4 (M := M))) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) (Litex.denote _value_i7)).mpr ⟨h_340, (Eq.mpr rfl (True.intro : (fun (_raw_i7 : M.Value) => True) (Litex.denote _value_i7)))⟩
          exact (Litex.piecewiseFn_call_eq (_object_i6 (M := M)) (⟨(fun (_input : M.Value) => (fun (_raw_i7 : M.Value) => (_raw_i7 = (M.number (3 : ℂ)))) _input), (fun (_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.number (30 : ℂ))) _input)⟩ : Litex.FunctionBranch M) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (Litex.denote _value_i7) _case_domain (Eq.mpr rfl (h_168 : (fun (_raw_i7 : M.Value) => (_raw_i7 = (M.number (3 : ℂ)))) (Litex.denote _value_i7)))).trans rfl)
      )
  )

noncomputable def _object_w51 := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
Litex.callOnDomain (_object_i4 (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) (_object_i6 (M := M)) _litex_call_arg_0 (h_352 (M := M)) (by
  let _atomic_wd_1_1 := (_object_i4 (M := M))
  exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (2 : ℂ) (1 : ℤ) (3 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro)

theorem h_359 : (by
  let _equal_wd_1_0 := (_object_w51 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (20 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w51 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (20 : ℂ)) from (by
          let _checked_call := _equal_wd_1_0
          let _case_arg_0 := (Litex.number (M := M) (2 : ℂ))
          have _case_requirement_0 : (by
            let _atomic_wd_1_1 := (_object_i4 (M := M))
            exact Litex.In (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_1) := (by
            let _atomic_wd_1_1 := (_object_i4 (M := M))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (2 : ℂ) (1 : ℤ) (3 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))
          have _checked_case_guard : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
          have _selected_beta := (h_356 (M := M)) _case_arg_0 _case_requirement_0 _checked_case_guard
          exact _selected_beta.trans (show @Eq M.Value _ _ from Eq.refl _))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_integer_x5f_row_x5f_cases_x2f_statement_x2e_lit
