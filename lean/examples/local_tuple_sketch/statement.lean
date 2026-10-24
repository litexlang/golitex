import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_tuple_x5f_sketch_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

include M in
private theorem _sketch_1 : True := by
  let _object_i1 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
  have h_3 : Litex.Same _object_i1 (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i)))) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i)))))
        )
    )
  have h_11 : Litex.In _object_i1 (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.union _wd_2_0 _wd_2_1));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0);
    let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
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
            let _membership_function := _object_i1
            let _membership_target := (by
              have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := by
                intro _raw_i2 h_6 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6)
                have h_6 : Litex.In _value_i2 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_6
                exact True.intro
              exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.union _wd_1_0 _wd_1_1))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.union _wd_1_0 _wd_1_1))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))
            have h_12 : (by
              let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0);
              let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0);
              (Litex.union _wd_1_0 _wd_1_1))
              exact Litex.In (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_1) := (by
              let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0);
              let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0);
              (Litex.union _wd_1_0 _wd_1_1))
              exact ((Litex.inUnion_iff (Litex.number (M := M) (2 : ℂ)) (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0) (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)).mpr (Or.inl (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact (by
                  let _set := _atomic_wd_2_1
                  exact ((Litex.inInsert_iff (Litex.number (M := M) (2 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _))))))))
            have h_13 : (by
              let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0);
              let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0);
              (Litex.union _wd_1_0 _wd_1_1))
              exact Litex.In (Litex.number (M := M) (3 : ℂ)) _atomic_wd_1_1) := (by
              let _atomic_wd_1_1 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0);
              let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0);
              (Litex.union _wd_1_0 _wd_1_1))
              exact ((Litex.inUnion_iff (Litex.number (M := M) (3 : ℂ)) (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0) (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)).mpr (Or.inr (by
                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
                  let _setTail_1 := Litex.emptySet (M := M);
                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                  _setTail_0)
                exact (by
                  let _set := _atomic_wd_2_1
                  exact ((Litex.inInsert_iff (Litex.number (M := M) (3 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _))))))))
            exact (by
            let _source_cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i)))))
            have _source_member : Litex.In _membership_function _source_cart := (by
            let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
            let _receiver := _object_i1
            have _same : Litex.Same _receiver _tuple := h_3
            exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
            have _domain : _membership_target.val.domain = Litex.FiniteFunction.indexSet (M := M) 2 := by
              change Litex.finiteSeqDomain (Litex.number (M := M) (2 : ℂ)) = _
              exact Litex.finiteSeqDomain_ofDenote (M := M) (Litex.number (M := M) (2 : ℂ)) 2 (by change M.number (2 : ℂ) = M.number ((2 : ℕ) : ℂ); norm_num)
            apply Litex.cartMemberInFnSetOfReturns _membership_function _source_cart _membership_target.val _source_member _domain
            let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
            have _same : Litex.Same _membership_function _tuple := h_3
            have _values : ∀ i : Fin 2, M.mem (_tuple.val.values i) _membership_target.val.output := (by
            have _finiteProof_0 := (h_12)
            have _finiteProof_1 := (h_13)
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

  let _object_h41 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.union _wd_2_0 _wd_2_1));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0);
    let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0);
    (Litex.union _wd_2_0 _wd_2_1))
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))

  have h_41 : Litex.In _object_i1 _object_h41 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _object_i1 _object_i1 (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.union _wd_2_0 _wd_2_1));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.union _wd_2_0 _wd_2_1))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h41 (Litex.sameRefl _object_i1) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.union _wd_2_0 _wd_2_1));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (3 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.union _wd_2_0 _wd_2_1))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_11)
        )
    )

  have h_29 : (by
    let _equal_wd_1_0 := (let _receiver := _object_i1;
    let _argument := (Litex.number (M := M) (1 : ℂ));
    let _cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i)))));
    Litex.cartCall _receiver _cart _argument (by
      let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
      let _receiver := _object_i1
      have _same : Litex.Same _receiver _tuple := h_3
      exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
      (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 2) (2 : ℂ) (by norm_num) (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
            have _receiver_eq : Litex.Same _object_i1 _tuple := h_3
            have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (1 : ℂ))) _receiver_eq
            have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (1 : ℂ)) = _tuple.val.values (0 : Fin 2) := by
              simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (0 : Fin 2))
            have _target_eq : _tuple.val.values (0 : Fin 2) = Litex.denote (Litex.number (M := M) (2 : ℂ)) := rfl
            exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)
          )
        )
    )

  have h_35 : (by
    let _equal_wd_1_0 := (let _receiver := _object_i1;
    let _argument := (Litex.number (M := M) (2 : ℂ));
    let _cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i)))));
    Litex.cartCall _receiver _cart _argument (by
      let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
      let _receiver := _object_i1
      have _same : Litex.Same _receiver _tuple := h_3
      exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
      (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 2) (2 : ℂ) (by norm_num) (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
            have _receiver_eq : Litex.Same _object_i1 _tuple := h_3
            have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (2 : ℂ))) _receiver_eq
            have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (2 : ℂ)) = _tuple.val.values (1 : Fin 2) := by
              simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (1 : Fin 2))
            have _target_eq : _tuple.val.values (1 : Fin 2) = Litex.denote (Litex.number (M := M) (3 : ℂ)) := rfl
            exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)
          )
        )
    )
  have h_1 : (by
    let _equal_wd_1_0 := (let _receiver := _object_i1;
    let _argument := (Litex.number (M := M) (1 : ℂ));
    let _cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i)))));
    Litex.cartCall _receiver _cart _argument (by
      let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
      let _receiver := _object_i1
      have _same : Litex.Same _receiver _tuple := h_3
      exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
      (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 2) (2 : ℂ) (by norm_num) (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          h_29
        )
    )
  have h_2 : (by
    let _equal_wd_1_0 := (let _receiver := _object_i1;
    let _argument := (Litex.number (M := M) (2 : ℂ));
    let _cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i)))));
    Litex.cartCall _receiver _cart _argument (by
      let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (2 : ℂ)), Litex.denote (Litex.number (M := M) (3 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (3 : ℂ))) (fun i => Fin.elim0 i))))
      let _receiver := _object_i1
      have _same : Litex.Same _receiver _tuple := h_3
      exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
      (Litex.indexSetMemberOfClosedRangeOfEq (p := _argument) (n := 2) (2 : ℂ) (by norm_num) (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          h_35
        )
    )
  exact True.intro
end LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_tuple_x5f_sketch_x2f_statement_x2e_lit
