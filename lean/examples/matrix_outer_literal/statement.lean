import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_outer_x5f_literal_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_w21 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))));
let _wd_1_1 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (4 : ℂ)), Litex.denote (Litex.number (M := M) (5 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (4 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (5 : ℂ))) (fun i => Fin.elim0 i))));
let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
let _wd_1_3 := (Litex.number (M := M) (2 : ℂ));
(Litex.matrixOuter _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
  let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
  let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
  exact (by
    let _membership_function := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
    let _membership_target := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
        intro _raw_i2 h_9 _
        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_9)
        have h_9 : Litex.In _value_i2 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_9
        have h_10 : Litex.In _value_i2 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_9).1
              )
          )
        have h_11 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_9).2.1
              )
          )
        have h_12 : Litex.Le _value_i2 _wd_1_3 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 h_9).2.2
              )
          )
        have h_13 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_9)
              )
          )
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))
    have h_14 : Litex.In _wd_1_3 (Litex.C (M := M)) := (Litex.numberInC (M := M) (2 : ℂ))
    have h_15 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.C (M := M)) := (Litex.numberInC (M := M) (3 : ℂ))
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
      have _finiteProof_0 := (h_14)
      have _finiteProof_1 := (h_15)
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )
      intro _input _hin
      rw [_domain] at _hin
      obtain ⟨_index, rfl⟩ := (Litex.FiniteFunction.indexSet_members (M := M) (n := 2) _input).mp _hin
      have _coordinate := (congrArg (fun p => Litex.FunctionSemantics.callValue (M := M) p (Litex.FiniteFunction.index _index)) _same).trans (Litex.tuple_coordinate _tuple _index)
      change M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) _) _membership_target.val.output
      rw [_coordinate]
      exact _values _index))) (by
  let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (4 : ℂ)), Litex.denote (Litex.number (M := M) (5 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (4 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (5 : ℂ))) (fun i => Fin.elim0 i))))
  let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
  exact (by
    let _membership_function := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (4 : ℂ)), Litex.denote (Litex.number (M := M) (5 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (4 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (5 : ℂ))) (fun i => Fin.elim0 i))))
    let _membership_target := (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → True := (by
        intro _raw_i5 h_21 _
        let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_21)
        have h_21 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_21
        have h_22 : Litex.In _value_i5 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i5 h_21).1
              )
          )
        have h_23 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i5 h_21).2.1
              )
          )
        have h_24 : Litex.Le _value_i5 _wd_1_3 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i5 h_21).2.2
              )
          )
        have h_25 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_21)
              )
          )
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)))
    have h_26 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.C (M := M)) := (Litex.numberInC (M := M) (4 : ℂ))
    have h_27 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.C (M := M)) := (Litex.numberInC (M := M) (5 : ℂ))
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
      have _finiteProof_0 := (h_26)
      have _finiteProof_1 := (h_27)
      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
    )
      intro _input _hin
      rw [_domain] at _hin
      obtain ⟨_index, rfl⟩ := (Litex.FiniteFunction.indexSet_members (M := M) (n := 2) _input).mp _hin
      have _coordinate := (congrArg (fun p => Litex.FunctionSemantics.callValue (M := M) p (Litex.FiniteFunction.index _index)) _same).trans (Litex.tuple_coordinate _tuple _index)
      change M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) _) _membership_target.val.output
      rw [_coordinate]
      exact _values _index)))))

noncomputable def _object_w22 := (Litex.matrixSet (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))

theorem h_1 : (by
  let _atomic_wd_1_0 := (_object_w21 (M := M))
  let _atomic_wd_1_1 := (_object_w22 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w21 (M := M))
          let _atomic_wd_1_1 := (_object_w22 (M := M))
          exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixOuterInRealFnSet _litex_matrix (by
            let _atomic_wd_2_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
            let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → True := (by
                intro _raw_i11 h_34 _
                let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_34)
                have h_34 : Litex.In _value_i11 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_34
                have h_35 : Litex.In _value_i11 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i11 h_34).1
                      )
                  )
                have h_36 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i11 h_34).2.1
                      )
                  )
                have h_37 : Litex.Le _value_i11 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i11 h_34).2.2
                      )
                  )
                have h_38 : Litex.In _value_i11 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i11 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_34)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)))
            exact (by
              let _tuple := _atomic_wd_2_0
              let _signature := (_atomic_wd_2_1).val
              have _domain : _signature.domain = Litex.FiniteFunction.indexSet (M := M) 2 := by
                change Litex.finiteSeqDomain (Litex.number (M := M) (2 : ℂ)) = _
                exact Litex.finiteSeqDomain_number 2
              have _coordinates : ∀ i : Fin 2, M.mem (_tuple.val.values i) _signature.output := (by
              have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))
              have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )
              have _member := Litex.tupleInFunctionSet _tuple _signature _domain _coordinates
              exact Litex.inOfSame _tuple _atomic_wd_2_0 (Litex.fnSet _signature) _atomic_wd_2_1 ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) _member)) (by
            let _atomic_wd_2_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (4 : ℂ)), Litex.denote (Litex.number (M := M) (5 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (4 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (5 : ℂ))) (fun i => Fin.elim0 i))))
            let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i12 : M.Value) => True) _raw_i12) → True := (by
                intro _raw_i12 h_44 _
                let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_44)
                have h_44 : Litex.In _value_i12 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_44
                have h_45 : Litex.In _value_i12 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i12 h_44).1
                      )
                  )
                have h_46 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i12 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i12 h_44).2.1
                      )
                  )
                have h_47 : Litex.Le _value_i12 (Litex.number (M := M) (2 : ℂ)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i12 h_44).2.2
                      )
                  )
                have h_48 : Litex.In _value_i12 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i12 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_44)
                      )
                  )
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) => True) _litex_input)))
            exact (by
              let _tuple := _atomic_wd_2_0
              let _signature := (_atomic_wd_2_1).val
              have _domain : _signature.domain = Litex.FiniteFunction.indexSet (M := M) 2 := by
                change Litex.finiteSeqDomain (Litex.number (M := M) (2 : ℂ)) = _
                exact Litex.finiteSeqDomain_number 2
              have _coordinates : ∀ i : Fin 2, M.mem (_tuple.val.values i) _signature.output := (by
              have _finiteProof_0 := ((Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)))
              have _finiteProof_1 := ((Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )
              have _member := Litex.tupleInFunctionSet _tuple _signature _domain _coordinates
              exact Litex.inOfSame _tuple _atomic_wd_2_0 (Litex.fnSet _signature) _atomic_wd_2_1 ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) _member))))))
      )
  )

noncomputable def _object_h51 := (Litex.fnSet (Litex.matrixSignature (_object_w22 (M := M))))

theorem h_51 : Litex.In (_object_w21 (M := M)) (_object_h51 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (_object_w21 (M := M)) (_object_w21 (M := M)) (_object_w22 (M := M)) (_object_h51 (M := M)) (Litex.sameRefl (_object_w21 (M := M))) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (_object_w22 (M := M)))) (h_1 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_outer_x5f_literal_x2f_statement_x2e_lit
