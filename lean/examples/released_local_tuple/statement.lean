import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_local_x5f_tuple_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_5 : Litex.In _value_i2 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))));
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
  exact Litex.Same _equal_wd_1_0 _value_i2) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_5
          have h_21 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have h_22 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          let _object_i3 := (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))))
          have h_23 : Litex.Same _object_i3 (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i)))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i)))))
                )
            )
          have h_39 : Litex.In _object_i3 (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i1;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_2_1 := (let _setElement_0 := _value_i2;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.union _wd_2_0 _wd_2_1));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i1;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_2_1 := (let _setElement_0 := _value_i2;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.union _wd_2_0 _wd_2_1))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _membership_function := _object_i3
                    let _membership_target := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                        intro _raw_i6 h_34 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_34)
                        have h_34 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_34
                        have h_35 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 h_34).1
                              )
                          )
                        have h_36 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 h_34).2.1
                              )
                          )
                        have h_37 : Litex.Le _value_i6 (Litex.number (M := M) (2 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 h_34).2.2
                              )
                          )
                        have h_38 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_34)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (let _wd_1_0 := (let _setElement_0 := _value_i1;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    let _wd_1_1 := (let _setElement_0 := _value_i2;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    (Litex.union _wd_1_0 _wd_1_1)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)))
                    have h_40 : (by
                      let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := _value_i1;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0);
                      let _wd_1_1 := (let _setElement_0 := _value_i2;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0);
                      (Litex.union _wd_1_0 _wd_1_1))
                      exact Litex.In _value_i1 _atomic_wd_1_1) := (by
                      let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := _value_i1;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0);
                      let _wd_1_1 := (let _setElement_0 := _value_i2;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0);
                      (Litex.union _wd_1_0 _wd_1_1))
                      exact ((Litex.inUnion_iff _value_i1 (let _setElement_0 := _value_i1;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0) (let _setElement_0 := _value_i2;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)).mpr (Or.inl (by
                        let _atomic_wd_2_1 := (let _setElement_0 := _value_i1;
                          let _setTail_1 := Litex.emptySet (M := M);
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact (by
                          let _set := _atomic_wd_2_1
                          exact ((Litex.inInsert_iff _value_i1 _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _))))))))
                    have h_41 : (by
                      let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := _value_i1;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0);
                      let _wd_1_1 := (let _setElement_0 := _value_i2;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0);
                      (Litex.union _wd_1_0 _wd_1_1))
                      exact Litex.In _value_i2 _atomic_wd_1_1) := (by
                      let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := _value_i1;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0);
                      let _wd_1_1 := (let _setElement_0 := _value_i2;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0);
                      (Litex.union _wd_1_0 _wd_1_1))
                      exact ((Litex.inUnion_iff _value_i2 (let _setElement_0 := _value_i1;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0) (let _setElement_0 := _value_i2;
                        let _setTail_1 := Litex.emptySet (M := M);
                        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                        _setTail_0)).mpr (Or.inr (by
                        let _atomic_wd_2_1 := (let _setElement_0 := _value_i2;
                          let _setTail_1 := Litex.emptySet (M := M);
                          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                          _setTail_0)
                        exact (by
                          let _set := _atomic_wd_2_1
                          exact ((Litex.inInsert_iff _value_i2 _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _))))))))
                    exact (by
                    let _source_cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i)))))
                    have _source_member : Litex.In _membership_function _source_cart := (by
                    let _tuple := (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))))
                    let _receiver := _object_i3
                    have _same : Litex.Same _receiver _tuple := h_23
                    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
                    have _domain : _membership_target.val.domain = Litex.FiniteFunction.indexSet (M := M) 2 := by
                      change Litex.finiteSeqDomain (Litex.number (M := M) (2 : ℂ)) = _
                      exact Litex.finiteSeqDomain_ofDenote (M := M) (Litex.number (M := M) (2 : ℂ)) 2 (by change M.number (2 : ℂ) = M.number ((2 : ℕ) : ℂ); norm_num)
                    apply Litex.cartMemberInFnSetOfReturns _membership_function _source_cart _membership_target.val _source_member _domain
                    let _tuple := (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))))
                    have _same : Litex.Same _membership_function _tuple := h_23
                    have _values : ∀ i : Fin 2, M.mem (_tuple.val.values i) _membership_target.val.output := (by
                    have _finiteProof_0 := (h_40)
                    have _finiteProof_1 := (h_41)
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

          let _object_h207 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i1;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_2_1 := (let _setElement_0 := _value_i2;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.union _wd_2_0 _wd_2_1));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i1;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_2_1 := (let _setElement_0 := _value_i2;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.union _wd_2_0 _wd_2_1))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))

          have h_207 : Litex.In _object_i3 _object_h207 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_i3 _object_i3 (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i1;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_2_1 := (let _setElement_0 := _value_i2;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.union _wd_2_0 _wd_2_1));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i1;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    let _wd_2_1 := (let _setElement_0 := _value_i2;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    (Litex.union _wd_2_0 _wd_2_1))
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h207 (Litex.sameRefl _object_i3) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i1;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  let _wd_2_1 := (let _setElement_0 := _value_i2;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.union _wd_2_0 _wd_2_1));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := _value_i1;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    let _wd_2_1 := (let _setElement_0 := _value_i2;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    (Litex.union _wd_2_0 _wd_2_1))
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_39)
                )
            )

          have h_171 : (by
            let _equal_wd_1_0 := (let _receiver := _object_i3;
            let _argument := (Litex.number (M := M) (1 : ℂ));
            let _cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i)))));
            Litex.cartCall _receiver _cart _argument (by
              let _tuple := (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))))
              let _receiver := _object_i3
              have _same : Litex.Same _receiver _tuple := h_23
              exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
              (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 2) (2 : ℂ) (by norm_num) (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _tuple := (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))))
                    have _receiver_eq : Litex.Same _object_i3 _tuple := h_23
                    have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (1 : ℂ))) _receiver_eq
                    have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (1 : ℂ)) = _tuple.val.values (0 : Fin 2) := by
                      simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (0 : Fin 2))
                    have _target_eq : _tuple.val.values (0 : Fin 2) = Litex.denote _value_i1 := rfl
                    exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)
                  )
                )
            )

          have h_189 : (by
            let _equal_wd_1_0 := (let _receiver := _object_i3;
            let _argument := (Litex.number (M := M) (2 : ℂ));
            let _cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i)))));
            Litex.cartCall _receiver _cart _argument (by
              let _tuple := (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))))
              let _receiver := _object_i3
              have _same : Litex.Same _receiver _tuple := h_23
              exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
              (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 2) (2 : ℂ) (by norm_num) (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))
            exact Litex.Same _equal_wd_1_0 _value_i2) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _tuple := (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))))
                    have _receiver_eq : Litex.Same _object_i3 _tuple := h_23
                    have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (2 : ℂ))) _receiver_eq
                    have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (2 : ℂ)) = _tuple.val.values (1 : Fin 2) := by
                      simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (1 : Fin 2))
                    have _target_eq : _tuple.val.values (1 : Fin 2) = Litex.denote _value_i2 := rfl
                    exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)
                  )
                )
            )
          have h_3 : (by
            let _equal_wd_1_0 := (let _receiver := _object_i3;
            let _argument := (Litex.number (M := M) (2 : ℂ));
            let _cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i)))));
            Litex.cartCall _receiver _cart _argument (by
              let _tuple := (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))))
              let _receiver := _object_i3
              have _same : Litex.Same _receiver _tuple := h_23
              exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
              (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 2) (2 : ℂ) (by norm_num) (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))
            exact Litex.Same _equal_wd_1_0 _value_i2) :=
            (by
              litex_checked_step =>
                exact (
                  h_189
                )
            )
          exact (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))));
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
          (show Litex.Same _equal_wd_1_0 _value_i2 from (by
            let _tuple := (_equal_wd_1_0).val.function
            have _receiver_eq : Litex.Same (_equal_wd_1_0).val.function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
            have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (2 : ℂ))) _receiver_eq
            have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (2 : ℂ)) = _tuple.val.values (1 : Fin 2) := by
              simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (1 : Fin 2))
            have _target_eq : _tuple.val.values (1 : Fin 2) = Litex.denote _value_i2 := rfl
            exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)
          )))
        )
      )
  )

theorem h_255 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (3 : ℂ)), Litex.denote (Litex.number (M := M) (4 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (4 : ℂ))) (fun i => Fin.elim0 i))));
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
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_256 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
                )
            )
          have h_257 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))
                )
            )
          have h_258 : Litex.Same (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (3 : ℂ)), Litex.denote (Litex.number (M := M) (4 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (4 : ℂ))) (fun i => Fin.elim0 i))));
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
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))) (Litex.number (M := M) (4 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2 (M := M)) (Litex.number (M := M) (3 : ℂ)) h_256 (Litex.number (M := M) (4 : ℂ)) h_257)
                )
            )
          exact (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (3 : ℂ)), Litex.denote (Litex.number (M := M) (4 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (4 : ℂ))) (fun i => Fin.elim0 i))));
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
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_258).trans (Litex.sameRefl (Litex.number (M := M) (4 : ℂ)))))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_local_x5f_tuple_x2f_statement_x2e_lit
