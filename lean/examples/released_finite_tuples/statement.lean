import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_finite_x5f_tuples_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_8 : Litex.In (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i)) (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0);
let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _membership_function := (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i))
          let _membership_target := (let _checked_header : ∀ (_raw_i1 : M.Value), M.mem _raw_i1 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)))) → ((fun (_raw_i1 : M.Value) => True) _raw_i1) → True := (by
              intro _raw_i1 h_3 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_3)
              have h_3 : Litex.In _value_i1 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num))) := h_3
              have h_4 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num))) _value_i1 h_3).1
                    )
                )
              have h_5 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num))) _value_i1 h_3).2.1
                    )
                )
              have h_6 : Litex.Le _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num))) _value_i1 h_3).2.2
                    )
                )
              have h_7 : Litex.In _value_i1 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num))) _value_i1 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3)
                    )
                )
              exact True.intro);
            Litex.fnSet (let _litex_output := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input)))
          exact (by
          let _source_cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i)))
          have _source_member : Litex.In _membership_function _source_cart := (by
          let _tuple := (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i))
          let _receiver := (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i))
          have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
          exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
          have _domain : _membership_target.val.domain = Litex.FiniteFunction.indexSet (M := M) 0 := by
            change Litex.finiteSeqDomain (Litex.number (M := M) (0 : ℂ)) = _
            exact Litex.finiteSeqDomain_ofDenote (M := M) (Litex.number (M := M) (0 : ℂ)) 0 (by change M.number (0 : ℂ) = M.number ((0 : ℕ) : ℂ); norm_num)
          apply Litex.cartMemberInFnSetOfReturns _membership_function _source_cart _membership_target.val _source_member _domain
          let _tuple := (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i))
          have _same : Litex.Same _membership_function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
          have _values : ∀ i : Fin 0, M.mem (_tuple.val.values i) _membership_target.val.output := (fun i => Fin.elim0 i)
          intro _input _hin
          rw [_domain] at _hin
          obtain ⟨_index, rfl⟩ := (Litex.FiniteFunction.indexSet_members (M := M) (n := 0) _input).mp _hin
          have _coordinate := (congrArg (fun p => Litex.FunctionSemantics.callValue (M := M) p (Litex.FiniteFunction.index _index)) _same).trans (Litex.tuple_coordinate _tuple _index)
          change M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) _) _membership_target.val.output
          rw [_coordinate]
          exact _values _index))
      )
  )

noncomputable def _object_h11 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0);
let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))))))

theorem h_11 : Litex.In (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i)) (_object_h11 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i)) (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i)) (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
          _setTail_0);
        let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))) (_object_h11 (M := M)) (Litex.sameRefl (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i))) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
          _setTail_0);
        let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))))) (h_8 (M := M)))
      )
  )

theorem h_12 : (by
  let _atomic_wd_1_0 := (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i))
  let _atomic_wd_1_1 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0);
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i))
          let _atomic_wd_1_1 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0);
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))))
          exact (h_8 (M := M)))
      )
  )

noncomputable def _object_h17 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0);
let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))))))

theorem h_17 : Litex.In (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i)) (_object_h17 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i)) (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i)) (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
          _setTail_0);
        let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))) (_object_h17 (M := M)) (Litex.sameRefl (Litex.tuple (M := M) ![] (fun i => Fin.elim0 i))) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
          _setTail_0);
        let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))))) (h_12 (M := M)))
      )
  )

theorem h_42 : Litex.In (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i))) (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _membership_function := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i)))
          let _membership_target := (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → True := (by
              intro _raw_i5 h_36 _
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_36)
              have h_36 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))) := h_36
              have h_37 : Litex.In _value_i5 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))) _value_i5 h_36).1
                    )
                )
              have h_38 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))) _value_i5 h_36).2.1
                    )
                )
              have h_39 : Litex.Le _value_i5 (Litex.number (M := M) (1 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))) _value_i5 h_36).2.2
                    )
                )
              have h_40 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_36)
                    )
                )
              have h_41 : Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        obtain ⟨k, hk, hlo, hhi⟩ := Litex.inClosedRangeInteger (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))) _value_i5 (1 : ℤ) (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) h_36
                        have heq : k = (1 : ℤ) := by omega
                        exact hk.trans ((congrArg M.number (by norm_num [heq] : (k : ℂ) = (1 : ℂ))).trans ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).symm)
                      )
                    )
                )
              exact True.intro);
            Litex.fnSet (let _litex_output := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)))
          have h_43 : (by
            let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.In (Litex.number (M := M) (7 : ℂ)) _atomic_wd_1_1) := (by
            let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (by
              let _set := _atomic_wd_1_1
              exact ((Litex.inInsert_iff (Litex.number (M := M) (7 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _)))))
          exact (by
          let _source_cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i))))
          have _source_member : Litex.In _membership_function _source_cart := (by
          let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i)))
          let _receiver := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i)))
          have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
          exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
          have _domain : _membership_target.val.domain = Litex.FiniteFunction.indexSet (M := M) 1 := by
            change Litex.finiteSeqDomain (Litex.number (M := M) (1 : ℂ)) = _
            exact Litex.finiteSeqDomain_ofDenote (M := M) (Litex.number (M := M) (1 : ℂ)) 1 (by change M.number (1 : ℂ) = M.number ((1 : ℕ) : ℂ); norm_num)
          apply Litex.cartMemberInFnSetOfReturns _membership_function _source_cart _membership_target.val _source_member _domain
          let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i)))
          have _same : Litex.Same _membership_function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
          have _values : ∀ i : Fin 1, M.mem (_tuple.val.values i) _membership_target.val.output := (by
          have _finiteProof_0 := (h_43)
          exact (Fin.cases _finiteProof_0 (fun i => Fin.elim0 i))
        )
          intro _input _hin
          rw [_domain] at _hin
          obtain ⟨_index, rfl⟩ := (Litex.FiniteFunction.indexSet_members (M := M) (n := 1) _input).mp _hin
          have _coordinate := (congrArg (fun p => Litex.FunctionSemantics.callValue (M := M) p (Litex.FiniteFunction.index _index)) _same).trans (Litex.tuple_coordinate _tuple _index)
          change M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) _) _membership_target.val.output
          rw [_coordinate]
          exact _values _index))
      )
  )

noncomputable def _object_h106 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))))))

theorem h_106 : Litex.In (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i))) (_object_h106 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i))) (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i))) (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) (_object_h106 (M := M)) (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i)))) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))))) (h_42 (M := M)))
      )
  )

theorem h_76 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i)));
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (let _receiver := _wd_1_0;
  let _argument := _wd_1_1;
  let _cart := (Litex.tupleSingletonCart _wd_1_0);
  Litex.cartCall _receiver _cart _argument (by
    let _tuple := _wd_1_0
    let _receiver := _wd_1_0
    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
    (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 1) (1 : ℂ) (by norm_num) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (1 : ℂ) (1 : ℂ) (1 : ℤ) (1 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i)));
        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
        (let _receiver := _wd_1_0;
        let _argument := _wd_1_1;
        let _cart := (Litex.tupleSingletonCart _wd_1_0);
        Litex.cartCall _receiver _cart _argument (by
          let _tuple := _wd_1_0
          let _receiver := _wd_1_0
          have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
          exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
          (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 1) (1 : ℂ) (by norm_num) (by
          let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))
          exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (1 : ℂ) (1 : ℂ) (1 : ℤ) (1 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)) from (by
          let _tuple := (_equal_wd_1_0).val.function
          have _receiver_eq : Litex.Same (_equal_wd_1_0).val.function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
          have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (1 : ℂ))) _receiver_eq
          have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (1 : ℂ)) = _tuple.val.values (0 : Fin 1) := by
            simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (0 : Fin 1))
          have _target_eq : _tuple.val.values (0 : Fin 1) = Litex.denote (Litex.number (M := M) (7 : ℂ)) := rfl
          exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)
        )))
      )
  )

theorem h_107 : (by
  let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i)))
  let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i)))
          let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))))
          exact (h_42 (M := M)))
      )
  )

noncomputable def _object_h120 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))))))

theorem h_120 : Litex.In (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i))) (_object_h120 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i))) (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i))) (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) (_object_h120 (M := M)) (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i)))) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))))) (h_107 (M := M)))
      )
  )

theorem h_121 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (7 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (7 : ℂ))) (fun i => Fin.elim0 i)));
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (let _receiver := _wd_1_0;
  let _argument := _wd_1_1;
  let _cart := (Litex.tupleSingletonCart _wd_1_0);
  Litex.cartCall _receiver _cart _argument (by
    let _tuple := _wd_1_0
    let _receiver := _wd_1_0
    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
    (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 1) (1 : ℂ) (by norm_num) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (1 : ℂ) (1 : ℂ) (1 : ℤ) (1 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_76 (M := M))
      )
  )

theorem h_162 : Litex.In (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i)))) (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(Litex.union _wd_2_0 _wd_2_1));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.union _wd_2_0 _wd_2_1))
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _membership_function := (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))
          let _membership_target := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
              intro _raw_i10 h_157 _
              let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_157)
              have h_157 : Litex.In _value_i10 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_157
              have h_158 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i10 h_157).1
                    )
                )
              have h_159 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i10 h_157).2.1
                    )
                )
              have h_160 : Litex.Le _value_i10 (Litex.number (M := M) (2 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i10 h_157).2.2
                    )
                )
              have h_161 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_157)
                    )
                )
              exact True.intro);
            Litex.fnSet (let _litex_output := (let _wd_1_0 := (let _setElement_0 := (Litex.R (M := M));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.union _wd_1_0 _wd_1_1)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)))
          have h_163 : (by
            let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := (Litex.R (M := M));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.union _wd_1_0 _wd_1_1))
            exact Litex.In (Litex.R (M := M)) _atomic_wd_1_1) := (by
            let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := (Litex.R (M := M));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.union _wd_1_0 _wd_1_1))
            exact ((Litex.inUnion_iff (Litex.R (M := M)) (let _setElement_0 := (Litex.R (M := M));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)).mpr (Or.inl (by
              let _atomic_wd_2_1 := (let _setElement_0 := (Litex.R (M := M));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact (by
                let _set := _atomic_wd_2_1
                exact ((Litex.inInsert_iff (Litex.R (M := M)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _))))))))
          have h_164 : (by
            let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := (Litex.R (M := M));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.union _wd_1_0 _wd_1_1))
            exact Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) := (by
            let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := (Litex.R (M := M));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.union _wd_1_0 _wd_1_1))
            exact ((Litex.inUnion_iff (Litex.number (M := M) (1 : ℂ)) (let _setElement_0 := (Litex.R (M := M));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)).mpr (Or.inr (by
              let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact (by
                let _set := _atomic_wd_2_1
                exact ((Litex.inInsert_iff (Litex.number (M := M) (1 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _))))))))
          exact (by
          let _source_cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i)))))
          have _source_member : Litex.In _membership_function _source_cart := (by
          let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))
          let _receiver := (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))
          have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
          exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
          have _domain : _membership_target.val.domain = Litex.FiniteFunction.indexSet (M := M) 2 := by
            change Litex.finiteSeqDomain (Litex.number (M := M) (2 : ℂ)) = _
            exact Litex.finiteSeqDomain_ofDenote (M := M) (Litex.number (M := M) (2 : ℂ)) 2 (by change M.number (2 : ℂ) = M.number ((2 : ℕ) : ℂ); norm_num)
          apply Litex.cartMemberInFnSetOfReturns _membership_function _source_cart _membership_target.val _source_member _domain
          let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))
          have _same : Litex.Same _membership_function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
          have _values : ∀ i : Fin 2, M.mem (_tuple.val.values i) _membership_target.val.output := (by
          have _finiteProof_0 := (h_163)
          have _finiteProof_1 := (h_164)
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )
          intro _input _hin
          rw [_domain] at _hin
          obtain ⟨_index, rfl⟩ := (Litex.FiniteFunction.indexSet_members (M := M) (n := 2) _input).mp _hin
          have _coordinate := (congrArg (fun p => Litex.FunctionSemantics.callValue (M := M) p (Litex.FiniteFunction.index _index)) _same).trans (Litex.tuple_coordinate _tuple _index)
          change M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) _) _membership_target.val.output
          rw [_coordinate]
          exact _values _index))
      )
  )

noncomputable def _object_h600 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(Litex.union _wd_2_0 _wd_2_1));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.union _wd_2_0 _wd_2_1))
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))

theorem h_600 : Litex.In (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i)))) (_object_h600 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i)))) (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i)))) (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.union _wd_2_0 _wd_2_1));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.union _wd_2_0 _wd_2_1))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (_object_h600 (M := M)) (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.union _wd_2_0 _wd_2_1));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.union _wd_2_0 _wd_2_1))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (h_162 (M := M)))
      )
  )

theorem h_492 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))));
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (let _receiver := _wd_1_0;
  let _argument := _wd_1_1;
  let _cart := (Litex.tupleSingletonCart _wd_1_0);
  Litex.cartCall _receiver _cart _argument (by
    let _tuple := _wd_1_0
    let _receiver := _wd_1_0
    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
    (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 2) (2 : ℂ) (by norm_num) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))))
  exact Litex.Same _equal_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))));
        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
        (let _receiver := _wd_1_0;
        let _argument := _wd_1_1;
        let _cart := (Litex.tupleSingletonCart _wd_1_0);
        Litex.cartCall _receiver _cart _argument (by
          let _tuple := _wd_1_0
          let _receiver := _wd_1_0
          have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
          exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
          (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 2) (2 : ℂ) (by norm_num) (by
          let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
          exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))));
        (show Litex.Same _equal_wd_1_0 (Litex.R (M := M)) from (by
          let _tuple := (_equal_wd_1_0).val.function
          have _receiver_eq : Litex.Same (_equal_wd_1_0).val.function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
          have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (1 : ℂ))) _receiver_eq
          have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (1 : ℂ)) = _tuple.val.values (0 : Fin 2) := by
            simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (0 : Fin 2))
          have _target_eq : _tuple.val.values (0 : Fin 2) = Litex.denote (Litex.R (M := M)) := rfl
          exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)
        )))
      )
  )

theorem h_546 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (let _receiver := _wd_1_0;
  let _argument := _wd_1_1;
  let _cart := (Litex.tupleSingletonCart _wd_1_0);
  Litex.cartCall _receiver _cart _argument (by
    let _tuple := _wd_1_0
    let _receiver := _wd_1_0
    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
    (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 2) (2 : ℂ) (by norm_num) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (let _receiver := _wd_1_0;
        let _argument := _wd_1_1;
        let _cart := (Litex.tupleSingletonCart _wd_1_0);
        Litex.cartCall _receiver _cart _argument (by
          let _tuple := _wd_1_0
          let _receiver := _wd_1_0
          have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
          exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
          (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 2) (2 : ℂ) (by norm_num) (by
          let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
          exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (by
          let _tuple := (_equal_wd_1_0).val.function
          have _receiver_eq : Litex.Same (_equal_wd_1_0).val.function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
          have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (2 : ℂ))) _receiver_eq
          have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (2 : ℂ)) = _tuple.val.values (1 : Fin 2) := by
            simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (1 : Fin 2))
          have _target_eq : _tuple.val.values (1 : Fin 2) = Litex.denote (Litex.number (M := M) (1 : ℂ)) := rfl
          exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)
        )))
      )
  )

theorem h_601 : (by
  let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))
  let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.union _wd_2_0 _wd_2_1));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0);
    let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0);
    (Litex.union _wd_2_0 _wd_2_1))
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))
          let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.union _wd_2_0 _wd_2_1));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.union _wd_2_0 _wd_2_1))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))
          exact (h_162 (M := M)))
      )
  )

noncomputable def _object_h622 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(Litex.union _wd_2_0 _wd_2_1));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.union _wd_2_0 _wd_2_1))
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))

theorem h_622 : Litex.In (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i)))) (_object_h622 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i)))) (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i)))) (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.union _wd_2_0 _wd_2_1));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.union _wd_2_0 _wd_2_1))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (_object_h622 (M := M)) (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))))) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.union _wd_2_0 _wd_2_1));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.R (M := M));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.union _wd_2_0 _wd_2_1))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) (h_601 (M := M)))
      )
  )

theorem h_623 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.number (M := M) (1 : ℂ))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (fun i => Fin.elim0 i))));
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (let _receiver := _wd_1_0;
  let _argument := _wd_1_1;
  let _cart := (Litex.tupleSingletonCart _wd_1_0);
  Litex.cartCall _receiver _cart _argument (by
    let _tuple := _wd_1_0
    let _receiver := _wd_1_0
    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
    (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 2) (2 : ℂ) (by norm_num) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))))
  exact Litex.Same _equal_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (h_492 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_finite_x5f_tuples_x2f_statement_x2e_lit
