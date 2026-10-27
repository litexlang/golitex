import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_bounded_x5f_finite_x5f_aggregate_x5f_values_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_w21 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
  let _setTail_3 := Litex.emptySet (M := M);
  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.Z (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => _raw_i1) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i1 : M.Value), M.mem _raw_i1 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) → ((fun (_raw_i1 : M.Value) => True) _raw_i1) → M.mem ((fun (_raw_i1 : M.Value) => _raw_i1) _raw_i1) (Litex.denote (Litex.Z (M := M))) := (by
    intro _raw_i1 h_32 _
    let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_32)
    have h_32 : Litex.In _value_i1 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) := h_32
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
    change Litex.In _value_i1 (Litex.Z (M := M))
    exact h_33)
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote (Litex.Z (M := M))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard));
(Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (let _litex_output := (Litex.Z (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input)) (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
    let _setTail_3 := Litex.emptySet (M := M);
    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  let _finite_tail_3 := _finite_tail_2.val.tail;
  have _finite_3 : Litex.IsFiniteSet _finite_tail_3 := Litex.finiteSetEmpty;
  have _finite_2 := Litex.finiteSetInsert _finite_tail_2 _finite_3;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0)) (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
    let _setTail_3 := Litex.emptySet (M := M);
    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.insertSubset _set.val.element _set.val.tail _atomic_wd_1_1 _set.wd (by
    let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (1 : ℂ) (1 : ℤ) (3 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail _atomic_wd_1_1 _set.val.tail.wd (by
    let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (2 : ℂ) (1 : ℤ) (3 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.insertSubset _set.val.tail.val.tail.val.element _set.val.tail.val.tail.val.tail _atomic_wd_1_1 _set.val.tail.val.tail.wd (by
    let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (3 : ℂ) (1 : ℤ) (3 : ℤ) (3 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.emptySubset _atomic_wd_1_1)))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w21 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w21 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) (6 : ℂ) (6 : ℂ) (by
          let _aggregate := _equal_wd_1_0
          let _enumerated := (_equal_wd_1_0).val.set
          have _enumeration_same : Litex.Same _aggregate.val.set _enumerated := (show @Eq M.Value _ _ from Eq.refl _)
          let _collection_tail_0 := _enumerated
          let _collection_tail_1 := _collection_tail_0.val.tail
          let _collection_tail_2 := _collection_tail_1.val.tail
          let _collection_tail_3 := _collection_tail_2.val.tail
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (1 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFnOn (let _litex_output := (Litex.Z (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => _raw_i1) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i1 : M.Value), M.mem _raw_i1 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) → ((fun (_raw_i1 : M.Value) => True) _raw_i1) → M.mem ((fun (_raw_i1 : M.Value) => _raw_i1) _raw_i1) (Litex.denote (Litex.Z (M := M))) := (by
              intro _raw_i1 h_95 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_95)
              have h_95 : Litex.In _value_i1 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) := h_95
              have h_96 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_95).1
                    )
                )
              have h_97 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_95).2.1
                    )
                )
              have h_98 : Litex.Le _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_95).2.2
                    )
                )
              have h_99 : Litex.In _value_i1 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_95)
                    )
                )
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_96)
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote (Litex.Z (M := M))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (let _litex_call_arg_0 := _wd_1_1;
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.Z (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (1 : ℂ) (1 : ℤ) (3 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) _call.wd.2
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (1 : ℂ)) := rfl
            have _calculated : (M.number (1 : ℂ)) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFnOn (let _litex_output := (Litex.Z (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => _raw_i1) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i1 : M.Value), M.mem _raw_i1 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) → ((fun (_raw_i1 : M.Value) => True) _raw_i1) → M.mem ((fun (_raw_i1 : M.Value) => _raw_i1) _raw_i1) (Litex.denote (Litex.Z (M := M))) := (by
              intro _raw_i1 h_139 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_139)
              have h_139 : Litex.In _value_i1 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) := h_139
              have h_140 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_139).1
                    )
                )
              have h_141 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_139).2.1
                    )
                )
              have h_142 : Litex.Le _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_139).2.2
                    )
                )
              have h_143 : Litex.In _value_i1 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_139)
                    )
                )
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_140)
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote (Litex.Z (M := M))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (let _litex_call_arg_0 := _wd_1_1;
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.Z (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (2 : ℂ) (1 : ℤ) (3 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) _call.wd.2
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := rfl
            have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFnOn (let _litex_output := (Litex.Z (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => _raw_i1) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i1 : M.Value), M.mem _raw_i1 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) → ((fun (_raw_i1 : M.Value) => True) _raw_i1) → M.mem ((fun (_raw_i1 : M.Value) => _raw_i1) _raw_i1) (Litex.denote (Litex.Z (M := M))) := (by
              intro _raw_i1 h_183 _
              let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_183)
              have h_183 : Litex.In _value_i1 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) := h_183
              have h_184 : Litex.In _value_i1 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_183).1
                    )
                )
              have h_185 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_183).2.1
                    )
                )
              have h_186 : Litex.Le _value_i1 (Litex.number (M := M) (3 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 h_183).2.2
                    )
                )
              have h_187 : Litex.In _value_i1 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i1 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_183)
                    )
                )
              change Litex.In _value_i1 (Litex.Z (M := M))
              exact h_184)
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote (Litex.Z (M := M))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (let _litex_call_arg_0 := _wd_1_1;
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.Z (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (3 : ℂ) (1 : ℤ) (3 : ℤ) (3 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) _call.wd.2
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := rfl
            have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
          have _members_3 : ∀ x, M.mem x (Litex.denote _collection_tail_3) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
          have _number_2 : Litex.denote _collection_tail_2.val.element = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
          have _members_2 := Litex.finiteMembersInsert _collection_tail_2 (M.number (3 : ℂ)) [] _number_2 _members_3
          have _number_1 : Litex.denote _collection_tail_1.val.element = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
          have _members_1 := Litex.finiteMembersInsert _collection_tail_1 (M.number (2 : ℂ)) [M.number (3 : ℂ)] _number_1 _members_2
          have _number_0 : Litex.denote _collection_tail_0.val.element = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
          have _members_0 := Litex.finiteMembersInsert _collection_tail_0 (M.number (1 : ℂ)) [M.number (2 : ℂ), M.number (3 : ℂ)] _number_0 _members_1
          apply Litex.finiteAggregateOnListDenote _aggregate [(1 : ℂ), (2 : ℂ), (3 : ℂ)] (6 : ℂ)
          · intro x
            rw [_enumeration_same]
            exact _members_0 x
          · norm_num [List.toFinset_cons, List.toFinset_nil, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2]) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w43 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
  let _setTail_3 := Litex.emptySet (M := M);
  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.Z (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => _raw_i2) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => _raw_i2) _raw_i2) (Litex.denote (Litex.Z (M := M))) := (by
    intro _raw_i2 h_231 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_231)
    have h_231 : Litex.In _value_i2 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) := h_231
    have h_232 : Litex.In _value_i2 (Litex.Z (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_231).1
          )
      )
    have h_233 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_231).2.1
          )
      )
    have h_234 : Litex.Le _value_i2 (Litex.number (M := M) (3 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_231).2.2
          )
      )
    have h_235 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_231)
          )
      )
    change Litex.In _value_i2 (Litex.Z (M := M))
    exact h_232)
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote (Litex.Z (M := M))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard));
(Litex.finiteAggregateOn true _wd_1_0 _wd_1_1 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (let _litex_output := (Litex.Z (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
    let _setTail_3 := Litex.emptySet (M := M);
    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  let _finite_tail_3 := _finite_tail_2.val.tail;
  have _finite_3 : Litex.IsFiniteSet _finite_tail_3 := Litex.finiteSetEmpty;
  have _finite_2 := Litex.finiteSetInsert _finite_tail_2 _finite_3;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0)) (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
    let _setTail_3 := Litex.emptySet (M := M);
    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.insertSubset _set.val.element _set.val.tail _atomic_wd_1_1 _set.wd (by
    let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (1 : ℂ) (1 : ℤ) (3 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail _atomic_wd_1_1 _set.val.tail.wd (by
    let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (2 : ℂ) (1 : ℤ) (3 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.insertSubset _set.val.tail.val.tail.val.element _set.val.tail.val.tail.val.tail _atomic_wd_1_1 _set.val.tail.val.tail.wd (by
    let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (3 : ℂ) (1 : ℤ) (3 : ℤ) (3 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.emptySubset _atomic_wd_1_1)))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))

theorem h_200 : (by
  let _equal_wd_1_0 := (_object_w43 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w43 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) (6 : ℂ) (6 : ℂ) (by
          let _aggregate := _equal_wd_1_0
          let _enumerated := (_equal_wd_1_0).val.set
          have _enumeration_same : Litex.Same _aggregate.val.set _enumerated := (show @Eq M.Value _ _ from Eq.refl _)
          let _collection_tail_0 := _enumerated
          let _collection_tail_1 := _collection_tail_0.val.tail
          let _collection_tail_2 := _collection_tail_1.val.tail
          let _collection_tail_3 := _collection_tail_2.val.tail
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (1 : ℂ))) = (1 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFnOn (let _litex_output := (Litex.Z (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => _raw_i2) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => _raw_i2) _raw_i2) (Litex.denote (Litex.Z (M := M))) := (by
              intro _raw_i2 h_294 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_294)
              have h_294 : Litex.In _value_i2 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) := h_294
              have h_295 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_294).1
                    )
                )
              have h_296 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_294).2.1
                    )
                )
              have h_297 : Litex.Le _value_i2 (Litex.number (M := M) (3 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_294).2.2
                    )
                )
              have h_298 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_294)
                    )
                )
              change Litex.In _value_i2 (Litex.Z (M := M))
              exact h_295)
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote (Litex.Z (M := M))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (let _litex_call_arg_0 := _wd_1_1;
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.Z (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (1 : ℂ) (1 : ℤ) (3 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) _call.wd.2
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (1 : ℂ)) := rfl
            have _calculated : (M.number (1 : ℂ)) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (1 : ℂ))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (2 : ℂ))) = (2 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFnOn (let _litex_output := (Litex.Z (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => _raw_i2) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => _raw_i2) _raw_i2) (Litex.denote (Litex.Z (M := M))) := (by
              intro _raw_i2 h_338 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_338)
              have h_338 : Litex.In _value_i2 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) := h_338
              have h_339 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_338).1
                    )
                )
              have h_340 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_338).2.1
                    )
                )
              have h_341 : Litex.Le _value_i2 (Litex.number (M := M) (3 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_338).2.2
                    )
                )
              have h_342 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_338)
                    )
                )
              change Litex.In _value_i2 (Litex.Z (M := M))
              exact h_339)
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote (Litex.Z (M := M))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (let _litex_call_arg_0 := _wd_1_1;
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.Z (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (2 : ℂ) (1 : ℤ) (3 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) _call.wd.2
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := rfl
            have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (2 : ℂ))
          have _aggregate_term_2 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number (3 : ℂ))) = (3 : ℂ) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFnOn (let _litex_output := (Litex.Z (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => _raw_i2) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => _raw_i2) _raw_i2) (Litex.denote (Litex.Z (M := M))) := (by
              intro _raw_i2 h_382 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_382)
              have h_382 : Litex.In _value_i2 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) := h_382
              have h_383 : Litex.In _value_i2 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_382).1
                    )
                )
              have h_384 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_382).2.1
                    )
                )
              have h_385 : Litex.Le _value_i2 (Litex.number (M := M) (3 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 h_382).2.2
                    )
                )
              have h_386 : Litex.In _value_i2 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i2 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_382)
                    )
                )
              change Litex.In _value_i2 (Litex.Z (M := M))
              exact h_383)
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.denote (Litex.Z (M := M))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))) (Litex.isSet (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (let _litex_call_arg_0 := _wd_1_1;
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (Litex.Z (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (3 : ℂ) (1 : ℤ) (3 : ℤ) (3 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) _call.wd.2
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := rfl
            have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _argument : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number (3 : ℂ))
          have _members_3 : ∀ x, M.mem x (Litex.denote _collection_tail_3) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
          have _number_2 : Litex.denote _collection_tail_2.val.element = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
          have _members_2 := Litex.finiteMembersInsert _collection_tail_2 (M.number (3 : ℂ)) [] _number_2 _members_3
          have _number_1 : Litex.denote _collection_tail_1.val.element = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
          have _members_1 := Litex.finiteMembersInsert _collection_tail_1 (M.number (2 : ℂ)) [M.number (3 : ℂ)] _number_1 _members_2
          have _number_0 : Litex.denote _collection_tail_0.val.element = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
          have _members_0 := Litex.finiteMembersInsert _collection_tail_0 (M.number (1 : ℂ)) [M.number (2 : ℂ), M.number (3 : ℂ)] _number_0 _members_1
          apply Litex.finiteAggregateOnListDenote _aggregate [(1 : ℂ), (2 : ℂ), (3 : ℂ)] (6 : ℂ)
          · intro x
            rw [_enumeration_same]
            exact _members_0 x
          · norm_num [List.toFinset_cons, List.toFinset_nil, _aggregate_term_0, _aggregate_term_1, _aggregate_term_2]) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (by norm_num))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_bounded_x5f_finite_x5f_aggregate_x5f_values_x2f_statement_x2e_lit
