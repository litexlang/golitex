import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_tuple_x5f_function_x5f_carrier_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_w6 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))

noncomputable def _object_w7 := (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))

theorem h_1 : (by
  let _atomic_wd_1_0 := (_object_w6 (M := M))
  let _atomic_wd_1_1 := (_object_w7 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w6 (M := M))
          let _atomic_wd_1_1 := (_object_w7 (M := M))
          exact (by
            let _membership_function := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
            let _membership_target := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                intro _raw_i2 h_6 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
                have h_6 : Litex.In _value_i2 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_6
                have h_7 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_6).1
                      )
                  )
                have h_8 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_6).2.1
                      )
                  )
                have h_9 : Litex.Le _value_i2 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_6).2.2
                      )
                  )
                have h_10 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))
            have h_11 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
            have h_12 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
            exact (by
              let _source_cart := (Litex.tupleSingletonCart _atomic_wd_1_0)
              have _source_member : Litex.In _membership_function _source_cart := (by
              let _tuple := _atomic_wd_1_0
              let _receiver := _atomic_wd_1_0
              have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
              exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
              have _domain : _membership_target.val.domain = Litex.FiniteFunction.indexSet (M := M) 2 := by
                change Litex.finiteSeqDomain (Litex.number (M := M) (2 : ℂ)) = _
                exact Litex.finiteSeqDomain_ofDenote (M := M) (Litex.number (M := M) (2 : ℂ)) 2 (by change M.number (2 : ℂ) = M.number ((2 : ℕ) : ℂ); norm_num)
              apply Litex.cartMemberInFnSetOfReturns _membership_function _source_cart _membership_target.val _source_member _domain
              let _tuple := _atomic_wd_1_0
              have _same : Litex.Same _membership_function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
              have _values : ∀ i : Fin 2, M.mem (_tuple.val.values i) _membership_target.val.output := (by
              have _finiteProof_0 := (h_11)
              have _finiteProof_1 := (h_12)
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )
              intro _input _hin
              rw [_domain] at _hin
              obtain ⟨_index, rfl⟩ := (Litex.FiniteFunction.indexSet_members (M := M) (n := 2) _input).mp _hin
              have _coordinate := (congrArg (fun p => Litex.FunctionSemantics.callValue (M := M) p (Litex.FiniteFunction.index _index)) _same).trans (Litex.tuple_coordinate _tuple _index)
              change M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) _) _membership_target.val.output
              rw [_coordinate]
              exact _values _index)))
      )
  )

noncomputable def _object_h13 := (Litex.fnSet (Litex.finiteSeqSignature (_object_w7 (M := M))))

theorem h_13 : Litex.In (_object_w6 (M := M)) (_object_h13 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (_object_w6 (M := M)) (_object_w6 (M := M)) (_object_w7 (M := M)) (_object_h13 (M := M)) (Litex.sameRefl (_object_w6 (M := M))) (Litex.finiteSeq_eq_fnSet (_object_w7 (M := M))) (h_1 (M := M)))
      )
  )

noncomputable def _object_i5 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (4 : ℂ)), Litex.denote (Litex.number (M := M) (5 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (4 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (5 : ℂ))) (fun i => Fin.elim0 i))))
theorem h_14 : Litex.Same (_object_i5 (M := M)) (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (4 : ℂ)), Litex.denote (Litex.number (M := M) (5 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (4 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (5 : ℂ))) (fun i => Fin.elim0 i)))) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (4 : ℂ)), Litex.denote (Litex.number (M := M) (5 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (4 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (5 : ℂ))) (fun i => Fin.elim0 i)))))
      )
  )

noncomputable def _object_w20 := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
    intro _raw_i6 h_26 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_26)
    have h_26 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_26
    have h_27 : Litex.In _value_i6 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 h_26).1
          )
      )
    have h_28 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 h_26).2.1
          )
      )
    have h_29 : Litex.Le _value_i6 (Litex.number (M := M) (2 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 h_26).2.2
          )
      )
    have h_30 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_26)
          )
      )
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)))

theorem h_15 : (by
  let _atomic_wd_1_1 := (_object_w20 (M := M))
  exact Litex.In (_object_i5 (M := M)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w20 (M := M))
          exact (by
            let _membership_function := (_object_i5 (M := M))
            let _membership_target := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                intro _raw_i6 h_49 _
                let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_49)
                have h_49 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_49
                have h_50 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 h_49).1
                      )
                  )
                have h_51 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 h_49).2.1
                      )
                  )
                have h_52 : Litex.Le _value_i6 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 h_49).2.2
                      )
                  )
                have h_53 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_49)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)))
            have h_54 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))
            have h_55 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))
            exact (by
              let _source_cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (4 : ℂ)), Litex.denote (Litex.number (M := M) (5 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (4 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (5 : ℂ))) (fun i => Fin.elim0 i)))))
              have _source_member : Litex.In _membership_function _source_cart := (by
              let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (4 : ℂ)), Litex.denote (Litex.number (M := M) (5 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (4 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (5 : ℂ))) (fun i => Fin.elim0 i))))
              let _receiver := (_object_i5 (M := M))
              have _same : Litex.Same _receiver _tuple := (h_14 (M := M))
              exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
              have _domain : _membership_target.val.domain = Litex.FiniteFunction.indexSet (M := M) 2 := by
                change Litex.finiteSeqDomain (Litex.number (M := M) (2 : ℂ)) = _
                exact Litex.finiteSeqDomain_ofDenote (M := M) (Litex.number (M := M) (2 : ℂ)) 2 (by change M.number (2 : ℂ) = M.number ((2 : ℕ) : ℂ); norm_num)
              apply Litex.cartMemberInFnSetOfReturns _membership_function _source_cart _membership_target.val _source_member _domain
              let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (4 : ℂ)), Litex.denote (Litex.number (M := M) (5 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (4 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (5 : ℂ))) (fun i => Fin.elim0 i))))
              have _same : Litex.Same _membership_function _tuple := (h_14 (M := M))
              have _values : ∀ i : Fin 2, M.mem (_tuple.val.values i) _membership_target.val.output := (by
              have _finiteProof_0 := (h_54)
              have _finiteProof_1 := (h_55)
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )
              intro _input _hin
              rw [_domain] at _hin
              obtain ⟨_index, rfl⟩ := (Litex.FiniteFunction.indexSet_members (M := M) (n := 2) _input).mp _hin
              have _coordinate := (congrArg (fun p => Litex.FunctionSemantics.callValue (M := M) p (Litex.FiniteFunction.index _index)) _same).trans (Litex.tuple_coordinate _tuple _index)
              change M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) _) _membership_target.val.output
              rw [_coordinate]
              exact _values _index)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_tuple_x5f_function_x5f_carrier_x2f_statement_x2e_lit
