import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_determinant_x5f_small_x5f_orders_x2f_statement_x2e_lit

universe u v1 v4 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_36 : Litex.In _value_i1 (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))), (by
  let _object_w3 := (Litex.matrixDeterminant _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
    exact h_36))
  exact (by
    let _equal_wd_1_0 := _object_w3
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_36
          let _object_h37 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))))
          have h_37 : Litex.In _value_i1 _object_h37 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))) _object_h37 (Litex.sameRefl _value_i1) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))))) h_36)
                )
            )
          let _object_w3 := (Litex.matrixDeterminant _value_i1 (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
            exact h_36))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w3
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (by
                    let _det := _equal_wd_1_0
                    let _expanded := (Litex.number (M := M) (1 : ℂ))
                    have _definition : Litex.Same _det _expanded := by
                      have _raw := Litex.matrixDeterminantZero (Litex.denote _det.val.matrix)
                      exact _raw
                    exact (_definition.trans (show @Eq M.Value _ _ from Eq.refl _))
                  )))
                )
            )
          exact h_1
        )
      )
  )

theorem h_79 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_113 : Litex.In _value_i4 (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))), (by
  let _object_h114 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))))
  have h_114 : Litex.In _value_i4 _object_h114 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))) _object_h114 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))))) h_113)
        )
    )
  let _object_w7 := (Litex.matrixDeterminant _value_i4 (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
    exact h_113))
  let _object_w8 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  let _litex_call_arg_1 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_114 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (1 : ℂ) (1 : ℂ) (1 : ℤ) (1 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (1 : ℂ) (1 : ℂ) (1 : ℤ) (1 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))) True.intro)
  exact (by
    let _equal_wd_1_0 := _object_w7
    let _equal_wd_1_1 := _object_w8
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_113
          let _object_h114 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))))
          have h_114 : Litex.In _value_i4 _object_h114 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))) _object_h114 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))))) h_113)
                )
            )
          let _object_w7 := (Litex.matrixDeterminant _value_i4 (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
            exact h_113))
          let _object_w8 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          let _litex_call_arg_1 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i4 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_114 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (1 : ℂ) (1 : ℂ) (1 : ℤ) (1 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (1 : ℂ) (1 : ℂ) (1 : ℤ) (1 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))) True.intro)
          have h_78 : (by
            let _equal_wd_1_0 := _object_w7
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w7;
                  let _equal_wd_1_1 := _object_w8;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _det := _equal_wd_1_0
                    let _expanded := _equal_wd_1_1
                    have _definition : Litex.Same _det _expanded := by
                      have _raw := Litex.matrixDeterminantOne (Litex.denote _det.val.matrix) _det.wd.2
                      simp only [Litex.matrixEntryValue, Nat.cast_one] at _raw
                      exact _raw
                    exact (_definition.trans (show @Eq M.Value _ _ from Eq.refl _))
                  )))
                )
            )
          exact h_78
        )
      )
  )

theorem h_246 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_280 : Litex.In _value_i7 (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))), (by
  let _object_h281 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))
  have h_281 : Litex.In _value_i7 _object_h281 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i7 _value_i7 (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))) _object_h281 (Litex.sameRefl _value_i7) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_280)
        )
    )
  let _object_w11 := (Litex.matrixDeterminant _value_i7 (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
    exact h_280))
  let _object_w12 := (let _wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  let _litex_call_arg_1 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i7 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_281 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))) True.intro);
  let _wd_2_1 := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
  let _litex_call_arg_1 := (Litex.number (M := M) (2 : ℂ));
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i7 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_281 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))) True.intro);
  (Litex.mul _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
  let _wd_1_1 := (let _wd_2_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  let _litex_call_arg_1 := (Litex.number (M := M) (2 : ℂ));
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i7 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_281 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))) True.intro);
  let _wd_2_1 := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
  let _litex_call_arg_1 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i7 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_281 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))) True.intro);
  (Litex.mul _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
  (Litex.sub _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _arithmetic := _atomic_wd_1_0
      exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (by
      let _arithmetic := _atomic_wd_1_0
      exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2))))
  exact (by
    let _equal_wd_1_0 := _object_w11
    let _equal_wd_1_1 := _object_w12
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_280
          let _object_h281 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))
          have h_281 : Litex.In _value_i7 _object_h281 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i7 _value_i7 (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))) _object_h281 (Litex.sameRefl _value_i7) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_280)
                )
            )
          let _object_w11 := (Litex.matrixDeterminant _value_i7 (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
            exact h_280))
          let _object_w12 := (let _wd_1_0 := (let _wd_2_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          let _litex_call_arg_1 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i7 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_281 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))) True.intro);
          let _wd_2_1 := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
          let _litex_call_arg_1 := (Litex.number (M := M) (2 : ℂ));
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i7 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_281 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))) True.intro);
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
          let _wd_1_1 := (let _wd_2_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          let _litex_call_arg_1 := (Litex.number (M := M) (2 : ℂ));
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i7 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_281 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))) True.intro);
          let _wd_2_1 := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
          let _litex_call_arg_1 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) (_raw_i9 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i7 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_281 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))) True.intro);
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _arithmetic := _atomic_wd_1_0
              exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _arithmetic := _atomic_wd_1_0
              exact Litex.mulInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2))))
          have h_245 : (by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w11;
                  let _equal_wd_1_1 := _object_w12;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _det := _equal_wd_1_0
                    let _expanded := _equal_wd_1_1
                    have _definition : Litex.Same _det _expanded := by
                      have _raw := Litex.matrixDeterminantTwo (Litex.denote _det.val.matrix) _det.wd.2
                      simp only [Litex.matrixEntryValue, Nat.cast_one, Nat.cast_ofNat] at _raw
                      exact _raw
                    exact (_definition.trans (show @Eq M.Value _ _ from Eq.refl _))
                  )))
                )
            )
          exact h_245
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_determinant_x5f_small_x5f_orders_x2f_statement_x2e_lit
