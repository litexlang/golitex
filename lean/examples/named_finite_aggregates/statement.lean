import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_finite_x5f_aggregates_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (4 : ℂ));
  let _setElement_2 := (Litex.number (M := M) (7 : ℂ));
  let _setTail_3 := Litex.emptySet (M := M);
  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (4 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (2 : ℂ) (4 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (2 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)
theorem h_9 : Litex.IsSet (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (4 : ℂ));
            let _setElement_2 := (Litex.number (M := M) (7 : ℂ));
            let _setTail_3 := Litex.emptySet (M := M);
            let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
            let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (4 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (2 : ℂ) (4 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (2 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (Litex.isSet _atomic_wd_1_0))
      )
  )
theorem h_10 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setElement_1 := (Litex.number (M := M) (4 : ℂ));
          let _setElement_2 := (Litex.number (M := M) (7 : ℂ));
          let _setTail_3 := Litex.emptySet (M := M);
          let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
          let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (4 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (4 : ℂ)) (2 : ℂ) (4 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (7 : ℂ)) (2 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0))
      )
  )

noncomputable def _object_i2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 (M.number (1 : ℂ)))) (by
  intro _raw_i3 h_24 _
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_24)
  have h_24 : Litex.In _value_i3 (Litex.Z (M := M)) := h_24
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i3 h_24) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i3 h_24) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInZ _value_i3 (Litex.number (M := M) (1 : ℂ)) h_24 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))))
theorem h_67 : Litex.In (_object_i2 (M := M)) (Litex.fnSet ((_object_i2 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i2 (M := M)))
      )
  )
theorem h_68 : Litex.Same (_object_i2 (M := M)) (_object_i2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i2 (M := M)))
      )
  )

noncomputable def _object_w6 := (Litex.finiteAggregate false (_object_i1 (M := M)) (_object_i2 (M := M)) .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) (Eq.mp (congrArg (fun (_set : M.Value) => (Litex.memberSet _set).Finite) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_10 (M := M)))).symm) (by
  let _atomic_wd_2_0 := (_object_i1 (M := M))
  exact (let _finite_tail_0 := _atomic_wd_2_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  let _finite_tail_3 := _finite_tail_2.val.tail;
  have _finite_3 : Litex.IsFiniteSet _finite_tail_3 := Litex.finiteSetEmpty;
  have _finite_2 := Litex.finiteSetInsert _finite_tail_2 _finite_3;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0))) (Litex.subsetOfSame (_object_i1 (M := M)) (Litex.Z (M := M)) (_object_i1 (M := M)) (Litex.Z (M := M)) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_10 (M := M)))).symm (Litex.sameRefl (Litex.Z (M := M))) (by
  let _atomic_wd_2_0 := (_object_i1 (M := M))
  exact (by
    let _set := _atomic_wd_2_0
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Z (M := M)) _set.wd (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Z (M := M)) _set.val.tail.wd (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.tail.val.element _set.val.tail.val.tail.val.tail (Litex.Z (M := M)) _set.val.tail.val.tail.wd (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num)) (Litex.emptySubset (Litex.Z (M := M))))))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.inOfSame (_object_i2 (M := M)) (_object_i2 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True))) (Litex.sameRefl (_object_i2 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)))) (h_67 (M := M))) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩))

theorem h_69 : (by
  let _equal_wd_1_0 := (_object_w6 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (16 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w6 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (16 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (16 : ℂ)) (16 : ℂ) (16 : ℂ) (by
          let _aggregate := _equal_wd_1_0
          let _enumerated := (_object_i1 (M := M))
          have _enumeration_same : Litex.Same _aggregate.val.set _enumerated := (h_10 (M := M))
          let _collection_tail_0 := _enumerated
          let _collection_tail_1 := _collection_tail_0.val.tail
          let _collection_tail_2 := _collection_tail_1.val.tail
          let _collection_tail_3 := _collection_tail_2.val.tail
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_67 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro)
            let _literal := (_object_i2 (M := M))
            have _head : Litex.Same _call.val.function _literal := (h_68 (M := M))
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) := rfl
            have _calculated : (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (4 : ℂ))) = (5 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (4 : ℂ)) (h_67 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) True.intro)
            let _literal := (_object_i2 (M := M))
            have _head : Litex.Same _call.val.function _literal := (h_68 (M := M))
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.addValue (M.number (4 : ℂ)) (M.number (1 : ℂ))) := rfl
            have _calculated : (M.addValue (M.number (4 : ℂ)) (M.number (1 : ℂ))) = M.number (5 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (4 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (5 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (7 : ℂ))) = (8 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (7 : ℂ)) (h_67 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num)) True.intro)
            let _literal := (_object_i2 (M := M))
            have _head : Litex.Same _call.val.function _literal := (h_68 (M := M))
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.addValue (M.number (7 : ℂ)) (M.number (1 : ℂ))) := rfl
            have _calculated : (M.addValue (M.number (7 : ℂ)) (M.number (1 : ℂ))) = M.number (8 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (7 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (7 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (8 : ℂ))
          have _members_3 : ∀ x, M.mem x (Litex.denote _collection_tail_3) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
          have _number_2 : Litex.denote _collection_tail_2.val.element = M.number (7 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (7 : ℂ)))
          have _members_2 := Litex.finiteMembersInsert _collection_tail_2 (M.number (7 : ℂ)) [] _number_2 _members_3
          have _number_1 : Litex.denote _collection_tail_1.val.element = M.number (4 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))
          have _members_1 := Litex.finiteMembersInsert _collection_tail_1 (M.number (4 : ℂ)) [M.number (7 : ℂ)] _number_1 _members_2
          have _number_0 : Litex.denote _collection_tail_0.val.element = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
          have _members_0 := Litex.finiteMembersInsert _collection_tail_0 (M.number (2 : ℂ)) [M.number (4 : ℂ), M.number (7 : ℂ)] _number_0 _members_1
          apply Litex.finiteAggregateListDenote _aggregate [(2 : ℂ), (4 : ℂ), (7 : ℂ)] (16 : ℂ)
          · intro x
            rw [_enumeration_same]
            exact _members_0 x
          · norm_num [List.toFinset_cons, List.toFinset_nil, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2]) (Litex.NativeBridge.denoteNumber (M := M) (16 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w8 := (Litex.finiteAggregate true (_object_i1 (M := M)) (_object_i2 (M := M)) .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) (Eq.mp (congrArg (fun (_set : M.Value) => (Litex.memberSet _set).Finite) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_10 (M := M)))).symm) (by
  let _atomic_wd_2_0 := (_object_i1 (M := M))
  exact (let _finite_tail_0 := _atomic_wd_2_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  let _finite_tail_3 := _finite_tail_2.val.tail;
  have _finite_3 : Litex.IsFiniteSet _finite_tail_3 := Litex.finiteSetEmpty;
  have _finite_2 := Litex.finiteSetInsert _finite_tail_2 _finite_3;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0))) (Litex.subsetOfSame (_object_i1 (M := M)) (Litex.Z (M := M)) (_object_i1 (M := M)) (Litex.Z (M := M)) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_10 (M := M)))).symm (Litex.sameRefl (Litex.Z (M := M))) (by
  let _atomic_wd_2_0 := (_object_i1 (M := M))
  exact (by
    let _set := _atomic_wd_2_0
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Z (M := M)) _set.wd (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Z (M := M)) _set.val.tail.wd (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.tail.val.element _set.val.tail.val.tail.val.tail (Litex.Z (M := M)) _set.val.tail.val.tail.wd (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num)) (Litex.emptySubset (Litex.Z (M := M))))))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.inOfSame (_object_i2 (M := M)) (_object_i2 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True))) (Litex.sameRefl (_object_i2 (M := M))) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)))) (h_67 (M := M))) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩))

theorem h_235 : (by
  let _equal_wd_1_0 := (_object_w8 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w8 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ)) (120 : ℂ) (120 : ℂ) (by
          let _aggregate := _equal_wd_1_0
          let _enumerated := (_object_i1 (M := M))
          have _enumeration_same : Litex.Same _aggregate.val.set _enumerated := (h_10 (M := M))
          let _collection_tail_0 := _enumerated
          let _collection_tail_1 := _collection_tail_0.val.tail
          let _collection_tail_2 := _collection_tail_1.val.tail
          let _collection_tail_3 := _collection_tail_2.val.tail
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_67 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro)
            let _literal := (_object_i2 (M := M))
            have _head : Litex.Same _call.val.function _literal := (h_68 (M := M))
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) := rfl
            have _calculated : (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (4 : ℂ))) = (5 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (4 : ℂ)) (h_67 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (4 : ℂ) (4 : ℤ) (by norm_num)) True.intro)
            let _literal := (_object_i2 (M := M))
            have _head : Litex.Same _call.val.function _literal := (h_68 (M := M))
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.addValue (M.number (4 : ℂ)) (M.number (1 : ℂ))) := rfl
            have _calculated : (M.addValue (M.number (4 : ℂ)) (M.number (1 : ℂ))) = M.number (5 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (4 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (5 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (7 : ℂ))) = (8 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) (Litex.number (M := M) (7 : ℂ)) (h_67 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num)) True.intro)
            let _literal := (_object_i2 (M := M))
            have _head : Litex.Same _call.val.function _literal := (h_68 (M := M))
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.addValue (M.number (7 : ℂ)) (M.number (1 : ℂ))) := rfl
            have _calculated : (M.addValue (M.number (7 : ℂ)) (M.number (1 : ℂ))) = M.number (8 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (7 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (7 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (8 : ℂ))
          have _members_3 : ∀ x, M.mem x (Litex.denote _collection_tail_3) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
          have _number_2 : Litex.denote _collection_tail_2.val.element = M.number (7 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (7 : ℂ)))
          have _members_2 := Litex.finiteMembersInsert _collection_tail_2 (M.number (7 : ℂ)) [] _number_2 _members_3
          have _number_1 : Litex.denote _collection_tail_1.val.element = M.number (4 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))
          have _members_1 := Litex.finiteMembersInsert _collection_tail_1 (M.number (4 : ℂ)) [M.number (7 : ℂ)] _number_1 _members_2
          have _number_0 : Litex.denote _collection_tail_0.val.element = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
          have _members_0 := Litex.finiteMembersInsert _collection_tail_0 (M.number (2 : ℂ)) [M.number (4 : ℂ), M.number (7 : ℂ)] _number_0 _members_1
          apply Litex.finiteAggregateListDenote _aggregate [(2 : ℂ), (4 : ℂ), (7 : ℂ)] (120 : ℂ)
          · intro x
            rw [_enumeration_same]
            exact _members_0 x
          · norm_num [List.toFinset_cons, List.toFinset_nil, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2]) (Litex.NativeBridge.denoteNumber (M := M) (120 : ℂ)) (by norm_num))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_finite_x5f_aggregates_x2f_statement_x2e_lit
