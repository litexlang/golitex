import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_factorial_x5f_identities_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.N (M := M))), (by
  let _object_w3 := (Litex.factorial _value_i1 h_17)
  have h_1 : (by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.In _atomic_wd_1_0 (Litex.NPos (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := _object_w3
            exact (Litex.factorialInNPos _atomic_wd_1_0))
        )
    )
  let _object_w5 := (let _wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i1 h_17) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.factorial _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInN _value_i1 (Litex.number (M := M) (1 : ℂ)) h_17 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))))))
  let _object_w6 := (let _wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i1 h_17) (Litex.numberInC (M := M) (1 : ℂ)));
  let _wd_1_1 := _object_w3;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i1 h_17) (Litex.numberInC (M := M) (1 : ℂ)))) (by
    let _atomic_wd_1_0 := _object_w3
    exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.inNPos_natural _atomic_wd_1_0 h_1)))))
  exact (((by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.In _atomic_wd_1_0 (Litex.NPos (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w3
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))) ∧ ((by
    let _equal_wd_1_0 := _object_w5
    let _equal_wd_1_1 := _object_w6
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17
          have h_18 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_17)
                )
            )
          let _object_w3 := (Litex.factorial _value_i1 h_17)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w3
            exact Litex.In _atomic_wd_1_0 (Litex.NPos (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact (Litex.factorialInNPos _atomic_wd_1_0))
                )
            )
          have h_28 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_w3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _object_w3 h_1)
                )
            )
          have h_29 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _object_w3 h_28)
                )
            )
          have h_30 : ¬ Litex.Same _object_w3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _object_w3 h_28) _litex_zero.symm)
                )
            )
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w3
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact h_30)
                )
            )
          let _object_w5 := (let _wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i1 h_17) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.factorial _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInN _value_i1 (Litex.number (M := M) (1 : ℂ)) h_17 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))))))
          let _object_w6 := (let _wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i1 h_17) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := _object_w3;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i1 h_17) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _object_w3
            exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.inNPos_natural _atomic_wd_1_0 h_1)))))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w5;
                  let _equal_wd_1_1 := _object_w6;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _upper := _equal_wd_1_0
                    let _lower := (_equal_wd_1_1).val.right
                    have _source_domain : Litex.In _value_i1 (Litex.N (M := M)) := h_17
                    let _u_native : ℂ := ((Litex.NativeBridge.asComplex _value_i1 (Litex.naturalToComplex _value_i1 h_17)) + (1 : ℂ))
                    have _u : Litex.denote _upper.val.arg = M.number _u_native := (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i1 h_17) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.naturalToComplex _value_i1 h_17)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))
                    let _l_native : ℂ := (Litex.NativeBridge.asComplex _value_i1 (Litex.naturalToComplex _value_i1 h_17))
                    have _l : Litex.denote _lower.val.arg = M.number _l_native := (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.naturalToComplex _value_i1 h_17))
                    let _c_native : ℂ := ((Litex.NativeBridge.asComplex _value_i1 (Litex.naturalToComplex _value_i1 h_17)) + (1 : ℂ))
                    have _c : Litex.denote (_equal_wd_1_1).val.left = M.number _c_native := (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i1 h_17) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.naturalToComplex _value_i1 h_17)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))
                    have _step : Litex.denote _upper.val.arg = M.addValue (Litex.denote _lower.val.arg) (M.number 1) := by
                      exact _u.trans ((congrArg M.number (by ring! : _u_native = _l_native + 1)).trans (((congrArg (fun _value => M.addValue _value (M.number 1)) _l).trans (M.add_numbers _l_native 1)).symm))
                    have _coefficient : Litex.denote (_equal_wd_1_1).val.left = Litex.denote _upper.val.arg := by
                      exact _c.trans ((congrArg M.number (by ring! : _c_native = _u_native)).trans _u.symm)
                    have _result : Litex.denote _upper = M.mulValue (Litex.denote (_equal_wd_1_1).val.left) (Litex.denote _lower) := by
                      rw [_coefficient]
                      exact Litex.factorialStep _upper _lower _step true
                    exact _result
                  )))
                )
            )
          exact (And.intro h_1 (And.intro h_2 h_3))
        )
      )
  )

theorem h_196 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_209 : Litex.In _value_i2 (Litex.NPos (M := M))), (by
  have h_210 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inNPos_positive _value_i2 h_209)
        )
    )
  let _object_w9 := (Litex.factorial _value_i2 (Litex.inNPos_natural _value_i2 h_209))
  let _object_w10 := (let _wd_1_0 := _value_i2;
  let _wd_1_1 := (let _wd_2_0 := (Litex.sub _wd_1_0 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _wd_1_0 (Litex.inNPos_natural _wd_1_0 h_209)) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.factorial _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.integerToNaturalOfNonnegative _atomic_wd_1_0 (by
      let _atomic_wd_2_0 := _atomic_wd_1_0
      exact (Litex.subInZ _wd_1_0 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToInteger _wd_1_0 (Litex.inNPos_natural _wd_1_0 h_209)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (by
      let _atomic_wd_2_1 := _atomic_wd_1_0
      exact (Litex.integerPredecessorLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_0 (Litex.inNPos_natural _wd_1_0 h_209)) (Litex.sameRefl (Litex.number (M := M) 1)) h_210))))));
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.naturalToComplex _wd_1_0 (Litex.inNPos_natural _wd_1_0 h_209)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.inNPos_natural _atomic_wd_1_0 (Litex.factorialInNPos _atomic_wd_1_0))))))
  exact (by
    let _equal_wd_1_0 := _object_w9
    let _equal_wd_1_1 := _object_w10
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_209
          have h_210 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i2 h_209)
                )
            )
          have h_211 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_210)
                )
            )
          have h_212 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_210) _litex_zero.symm)
                )
            )
          let _object_w9 := (Litex.factorial _value_i2 (Litex.inNPos_natural _value_i2 h_209))
          let _object_w10 := (let _wd_1_0 := _value_i2;
          let _wd_1_1 := (let _wd_2_0 := (Litex.sub _wd_1_0 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _wd_1_0 (Litex.inNPos_natural _wd_1_0 h_209)) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.factorial _wd_2_0 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.integerToNaturalOfNonnegative _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.subInZ _wd_1_0 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToInteger _wd_1_0 (Litex.inNPos_natural _wd_1_0 h_209)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (by
              let _atomic_wd_2_1 := _atomic_wd_1_0
              exact (Litex.integerPredecessorLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.naturalToInteger _wd_1_0 (Litex.inNPos_natural _wd_1_0 h_209)) (Litex.sameRefl (Litex.number (M := M) 1)) h_210))))));
          (Litex.mul _wd_1_0 _wd_1_1 (Litex.naturalToComplex _wd_1_0 (Litex.inNPos_natural _wd_1_0 h_209)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.inNPos_natural _atomic_wd_1_0 (Litex.factorialInNPos _atomic_wd_1_0))))))
          have h_195 : (by
            let _equal_wd_1_0 := _object_w9
            let _equal_wd_1_1 := _object_w10
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w9;
                  let _equal_wd_1_1 := _object_w10;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _upper := _equal_wd_1_0
                    let _lower := (_equal_wd_1_1).val.right
                    have _source_domain : Litex.In _value_i2 (Litex.NPos (M := M)) := h_209
                    let _u_native : ℂ := (Litex.NativeBridge.asComplex _value_i2 (Litex.naturalToComplex _value_i2 (Litex.inNPos_natural _value_i2 h_209)))
                    have _u : Litex.denote _upper.val.arg = M.number _u_native := (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.naturalToComplex _value_i2 (Litex.inNPos_natural _value_i2 h_209)))
                    let _l_native : ℂ := ((Litex.NativeBridge.asComplex _value_i2 (Litex.naturalToComplex _value_i2 (Litex.inNPos_natural _value_i2 h_209))) - (1 : ℂ))
                    have _l : Litex.denote _lower.val.arg = M.number _l_native := (Litex.NativeBridge.denoteSub _value_i2 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i2 (Litex.inNPos_natural _value_i2 h_209)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.naturalToComplex _value_i2 (Litex.inNPos_natural _value_i2 h_209))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))
                    let _c_native : ℂ := (Litex.NativeBridge.asComplex _value_i2 (Litex.naturalToComplex _value_i2 (Litex.inNPos_natural _value_i2 h_209)))
                    have _c : Litex.denote _value_i2 = M.number _c_native := (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.naturalToComplex _value_i2 (Litex.inNPos_natural _value_i2 h_209)))
                    have _step : Litex.denote _upper.val.arg = M.addValue (Litex.denote _lower.val.arg) (M.number 1) := by
                      exact _u.trans ((congrArg M.number (by ring! : _u_native = _l_native + 1)).trans (((congrArg (fun _value => M.addValue _value (M.number 1)) _l).trans (M.add_numbers _l_native 1)).symm))
                    have _coefficient : Litex.denote _value_i2 = Litex.denote _upper.val.arg := by
                      exact _c.trans ((congrArg M.number (by ring! : _c_native = _u_native)).trans _u.symm)
                    have _result : Litex.denote _upper = M.mulValue (Litex.denote _value_i2) (Litex.denote _lower) := by
                      rw [_coefficient]
                      exact Litex.factorialStep _upper _lower _step true
                    exact _result
                  )))
                )
            )
          exact h_195
        )
      )
  )

theorem h_2475 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_2488 : Litex.In _value_i3 (Litex.N (M := M))), (by
  let _object_w13 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_2488));
  (Litex.factorial _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInN (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) h_2488))))
  let _object_w14 := (let _wd_1_0 := (Litex.factorial _value_i3 h_2488);
  let _wd_1_1 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_2488) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.inNPos_natural _atomic_wd_1_0 (Litex.factorialInNPos _atomic_wd_1_0)))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.addInC _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_2488) (Litex.numberInC (M := M) (1 : ℂ))))))
  exact (by
    let _equal_wd_1_0 := _object_w13
    let _equal_wd_1_1 := _object_w14
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_2488
          have h_2489 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i3 h_2488)
                )
            )
          let _object_w13 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_2488));
          (Litex.factorial _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInN (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) h_2488))))
          let _object_w14 := (let _wd_1_0 := (Litex.factorial _value_i3 h_2488);
          let _wd_1_1 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_2488) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.inNPos_natural _atomic_wd_1_0 (Litex.factorialInNPos _atomic_wd_1_0)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.addInC _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_2488) (Litex.numberInC (M := M) (1 : ℂ))))))
          have h_2474 : (by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w13;
                  let _equal_wd_1_1 := _object_w14;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _upper := _equal_wd_1_0
                    let _lower := (_equal_wd_1_1).val.left
                    have _source_domain : Litex.In _value_i3 (Litex.N (M := M)) := h_2488
                    let _u_native : ℂ := ((1 : ℂ) + (Litex.NativeBridge.asComplex _value_i3 (Litex.naturalToComplex _value_i3 h_2488)))
                    have _u : Litex.denote _upper.val.arg = M.number _u_native := (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_2488) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.naturalToComplex _value_i3 h_2488)))
                    let _l_native : ℂ := (Litex.NativeBridge.asComplex _value_i3 (Litex.naturalToComplex _value_i3 h_2488))
                    have _l : Litex.denote _lower.val.arg = M.number _l_native := (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.naturalToComplex _value_i3 h_2488))
                    let _c_native : ℂ := ((Litex.NativeBridge.asComplex _value_i3 (Litex.naturalToComplex _value_i3 h_2488)) + (1 : ℂ))
                    have _c : Litex.denote (_equal_wd_1_1).val.right = M.number _c_native := (Litex.NativeBridge.denoteAdd _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i3 h_2488) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.naturalToComplex _value_i3 h_2488)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))
                    have _step : Litex.denote _upper.val.arg = M.addValue (Litex.denote _lower.val.arg) (M.number 1) := by
                      exact _u.trans ((congrArg M.number (by ring! : _u_native = _l_native + 1)).trans (((congrArg (fun _value => M.addValue _value (M.number 1)) _l).trans (M.add_numbers _l_native 1)).symm))
                    have _coefficient : Litex.denote (_equal_wd_1_1).val.right = Litex.denote _upper.val.arg := by
                      exact _c.trans ((congrArg M.number (by ring! : _c_native = _u_native)).trans _u.symm)
                    have _result : Litex.denote _upper = M.mulValue (Litex.denote _lower) (Litex.denote (_equal_wd_1_1).val.right) := by
                      rw [_coefficient]
                      exact Litex.factorialStep _upper _lower _step false
                    exact _result
                  )))
                )
            )
          exact h_2474
        )
      )
  )

theorem h_2605 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_2619 : Litex.In _value_i4 (Litex.NPos (M := M))), (by
  have h_2620 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inNPos_positive _value_i4 h_2619)
        )
    )
  let _object_w17 := (let _wd_1_0 := (let _wd_2_0 := (Litex.sub _value_i4 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i4 (Litex.inNPos_natural _value_i4 h_2619)) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.factorial _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.integerToNaturalOfNonnegative _atomic_wd_1_0 (by
      let _atomic_wd_2_0 := _atomic_wd_1_0
      exact (Litex.subInZ _value_i4 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToInteger _value_i4 (Litex.inNPos_natural _value_i4 h_2619)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (by
      let _atomic_wd_2_1 := _atomic_wd_1_0
      exact (Litex.integerPredecessorLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i4 (Litex.inNPos_natural _value_i4 h_2619)) (Litex.sameRefl (Litex.number (M := M) 1)) h_2620))))));
  let _wd_1_1 := _value_i4;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.inNPos_natural _atomic_wd_1_0 (Litex.factorialInNPos _atomic_wd_1_0)))) (Litex.naturalToComplex _wd_1_1 (Litex.inNPos_natural _wd_1_1 h_2619))))
  let _object_w18 := (Litex.factorial _value_i4 (Litex.inNPos_natural _value_i4 h_2619))
  exact (by
    let _equal_wd_1_0 := _object_w17
    let _equal_wd_1_1 := _object_w18
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_2619
          have h_2620 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i4 h_2619)
                )
            )
          have h_2621 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i4 h_2620)
                )
            )
          have h_2622 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i4 h_2620) _litex_zero.symm)
                )
            )
          let _object_w17 := (let _wd_1_0 := (let _wd_2_0 := (Litex.sub _value_i4 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i4 (Litex.inNPos_natural _value_i4 h_2619)) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.factorial _wd_2_0 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.integerToNaturalOfNonnegative _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.subInZ _value_i4 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToInteger _value_i4 (Litex.inNPos_natural _value_i4 h_2619)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (by
              let _atomic_wd_2_1 := _atomic_wd_1_0
              exact (Litex.integerPredecessorLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i4 (Litex.inNPos_natural _value_i4 h_2619)) (Litex.sameRefl (Litex.number (M := M) 1)) h_2620))))));
          let _wd_1_1 := _value_i4;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.inNPos_natural _atomic_wd_1_0 (Litex.factorialInNPos _atomic_wd_1_0)))) (Litex.naturalToComplex _wd_1_1 (Litex.inNPos_natural _wd_1_1 h_2619))))
          let _object_w18 := (Litex.factorial _value_i4 (Litex.inNPos_natural _value_i4 h_2619))
          have h_2604 : (by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w17;
                  let _equal_wd_1_1 := _object_w18;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _upper := _equal_wd_1_1
                    let _lower := (_equal_wd_1_0).val.left
                    have _source_domain : Litex.In _value_i4 (Litex.NPos (M := M)) := h_2619
                    let _u_native : ℂ := (Litex.NativeBridge.asComplex _value_i4 (Litex.naturalToComplex _value_i4 (Litex.inNPos_natural _value_i4 h_2619)))
                    have _u : Litex.denote _upper.val.arg = M.number _u_native := (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.naturalToComplex _value_i4 (Litex.inNPos_natural _value_i4 h_2619)))
                    let _l_native : ℂ := ((Litex.NativeBridge.asComplex _value_i4 (Litex.naturalToComplex _value_i4 (Litex.inNPos_natural _value_i4 h_2619))) - (1 : ℂ))
                    have _l : Litex.denote _lower.val.arg = M.number _l_native := (Litex.NativeBridge.denoteSub _value_i4 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i4 (Litex.inNPos_natural _value_i4 h_2619)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.naturalToComplex _value_i4 (Litex.inNPos_natural _value_i4 h_2619))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))
                    let _c_native : ℂ := (Litex.NativeBridge.asComplex _value_i4 (Litex.naturalToComplex _value_i4 (Litex.inNPos_natural _value_i4 h_2619)))
                    have _c : Litex.denote _value_i4 = M.number _c_native := (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.naturalToComplex _value_i4 (Litex.inNPos_natural _value_i4 h_2619)))
                    have _step : Litex.denote _upper.val.arg = M.addValue (Litex.denote _lower.val.arg) (M.number 1) := by
                      exact _u.trans ((congrArg M.number (by ring! : _u_native = _l_native + 1)).trans (((congrArg (fun _value => M.addValue _value (M.number 1)) _l).trans (M.add_numbers _l_native 1)).symm))
                    have _coefficient : Litex.denote _value_i4 = Litex.denote _upper.val.arg := by
                      exact _c.trans ((congrArg M.number (by ring! : _c_native = _u_native)).trans _u.symm)
                    have _result : Litex.denote _upper = M.mulValue (Litex.denote _lower) (Litex.denote _value_i4) := by
                      rw [_coefficient]
                      exact Litex.factorialStep _upper _lower _step false
                    exact _result.symm
                  )))
                )
            )
          exact h_2604
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_factorial_x5f_identities_x2f_statement_x2e_lit
