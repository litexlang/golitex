import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_finite_x5f_aggregates_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_23 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0);
  let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
    intro _raw_i1 h_37 _
    let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_37)
    have h_37 : Litex.In _value_i1 (Litex.Z (M := M)) := h_37
    change Litex.In _value_i1 (Litex.Z (M := M))
    exact h_37));
  (Litex.finiteAggregate false _wd_1_0 _wd_1_1 .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact (let _finite_tail_0 := _atomic_wd_1_0;
    have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
    _finite_0)) (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact (by
      let _set := _atomic_wd_1_0
      exact (Litex.emptySubset (Litex.Z (M := M))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
          _setTail_0);
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_37 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_37)
          have h_37 : Litex.In _value_i1 (Litex.Z (M := M)) := h_37
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_37));
        (Litex.finiteAggregate false _wd_1_0 _wd_1_1 .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
          _finite_0)) (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.emptySubset (Litex.Z (M := M))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) (((Eq.refl (Litex.denote (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
          _setTail_0);
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_14 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
          have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_14));
        (Litex.finiteAggregate false _wd_1_0 _wd_1_1 .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
          _finite_0)) (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.emptySubset (Litex.Z (M := M))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))))).trans (show (Litex.denote (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
          _setTail_0);
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_14 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
          have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
          change Litex.In _value_i1 (Litex.Z (M := M))
          exact h_14));
        (Litex.finiteAggregate false _wd_1_0 _wd_1_1 .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
          _finite_0)) (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.emptySubset (Litex.Z (M := M))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))) = M.number (0 : ℂ) from (by
          let _aggregate := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0);
          let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_14 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_14)
            have h_14 : Litex.In _value_i1 (Litex.Z (M := M)) := h_14
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_14));
          (Litex.finiteAggregate false _wd_1_0 _wd_1_1 .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact (let _finite_tail_0 := _atomic_wd_1_0;
            have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
            _finite_0)) (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact (by
              let _set := _atomic_wd_1_0
              exact (Litex.emptySubset (Litex.Z (M := M))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))
          apply Litex.finiteAggregateListDenote _aggregate [] (0 : ℂ)
          · exact (by
            let _enumerated := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            have _enumeration_same : Litex.Same (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0) _enumerated := (show @Eq M.Value _ _ from Eq.refl _)
            let _collection_tail_0 := _enumerated
            have _members_0 : ∀ x, M.mem x (Litex.denote _collection_tail_0) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
            intro x
            exact Eq.mpr (congrArg (fun _set => M.mem x _set ↔ x ∈ ([] : List M.Value)) _enumeration_same) (_members_0 x))
          · norm_num [List.toFinset_cons, List.toFinset_nil]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))).symm)))
      )
  )

noncomputable def _object_w6 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0);
let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
  intro _raw_i2 h_60 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_60)
  have h_60 : Litex.In _value_i2 (Litex.Z (M := M)) := h_60
  change Litex.In _value_i2 (Litex.Z (M := M))
  exact h_60));
(Litex.finiteAggregate false _wd_1_0 _wd_1_1 .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True)) (by
  let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
  _finite_0)) (by
  let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.emptySubset (Litex.Z (M := M))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))

theorem h_46 : (by
  let _equal_wd_1_0 := (_object_w6 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w6 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) ((show (Litex.denote _equal_wd_1_0) = M.number (0 : ℂ) from (by
          let _aggregate := _equal_wd_1_0
          apply Litex.finiteAggregateListDenote _aggregate [] (0 : ℂ)
          · exact (by
            let _enumerated := (_equal_wd_1_0).val.set
            have _enumeration_same : Litex.Same (_equal_wd_1_0).val.set _enumerated := (show @Eq M.Value _ _ from Eq.refl _)
            let _collection_tail_0 := _enumerated
            have _members_0 : ∀ x, M.mem x (Litex.denote _collection_tail_0) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
            intro x
            exact Eq.mpr (congrArg (fun _set => M.mem x _set ↔ x ∈ ([] : List M.Value)) _enumeration_same) (_members_0 x))
          · norm_num [List.toFinset_cons, List.toFinset_nil]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))).symm)))
      )
  )

theorem h_96 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0);
  let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
    intro _raw_i3 h_110 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_110)
    have h_110 : Litex.In _value_i3 (Litex.Z (M := M)) := h_110
    change Litex.In _value_i3 (Litex.Z (M := M))
    exact h_110));
  (Litex.finiteAggregate true _wd_1_0 _wd_1_1 .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact (let _finite_tail_0 := _atomic_wd_1_0;
    have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
    _finite_0)) (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact (by
      let _set := _atomic_wd_1_0
      exact (Litex.emptySubset (Litex.Z (M := M))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
          _setTail_0);
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
          intro _raw_i3 h_110 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_110)
          have h_110 : Litex.In _value_i3 (Litex.Z (M := M)) := h_110
          change Litex.In _value_i3 (Litex.Z (M := M))
          exact h_110));
        (Litex.finiteAggregate true _wd_1_0 _wd_1_1 .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
          _finite_0)) (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.emptySubset (Litex.Z (M := M))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) (((Eq.refl (Litex.denote (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
          _setTail_0);
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
          intro _raw_i3 h_87 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_87)
          have h_87 : Litex.In _value_i3 (Litex.Z (M := M)) := h_87
          change Litex.In _value_i3 (Litex.Z (M := M))
          exact h_87));
        (Litex.finiteAggregate true _wd_1_0 _wd_1_1 .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
          _finite_0)) (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.emptySubset (Litex.Z (M := M))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))))).trans (show (Litex.denote (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
          _setTail_0);
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
          intro _raw_i3 h_87 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_87)
          have h_87 : Litex.In _value_i3 (Litex.Z (M := M)) := h_87
          change Litex.In _value_i3 (Litex.Z (M := M))
          exact h_87));
        (Litex.finiteAggregate true _wd_1_0 _wd_1_1 .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
          _finite_0)) (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.emptySubset (Litex.Z (M := M))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))) = M.number (1 : ℂ) from (by
          let _aggregate := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0);
          let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => _raw_i3) (by
            intro _raw_i3 h_87 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_87)
            have h_87 : Litex.In _value_i3 (Litex.Z (M := M)) := h_87
            change Litex.In _value_i3 (Litex.Z (M := M))
            exact h_87));
          (Litex.finiteAggregate true _wd_1_0 _wd_1_1 .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i3 : M.Value) => True)) (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact (let _finite_tail_0 := _atomic_wd_1_0;
            have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
            _finite_0)) (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact (by
              let _set := _atomic_wd_1_0
              exact (Litex.emptySubset (Litex.Z (M := M))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))
          apply Litex.finiteAggregateListDenote _aggregate [] (1 : ℂ)
          · exact (by
            let _enumerated := ((_object_w6 (M := M))).val.set
            have _enumeration_same : Litex.Same ((_object_w6 (M := M))).val.set _enumerated := (show @Eq M.Value _ _ from Eq.refl _)
            let _collection_tail_0 := _enumerated
            have _members_0 : ∀ x, M.mem x (Litex.denote _collection_tail_0) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
            intro x
            exact Eq.mpr (congrArg (fun _set => M.mem x _set ↔ x ∈ ([] : List M.Value)) _enumeration_same) (_members_0 x))
          · norm_num [List.toFinset_cons, List.toFinset_nil]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))).symm)))
      )
  )

noncomputable def _object_w12 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0);
let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => _raw_i4) (by
  intro _raw_i4 h_133 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_133)
  have h_133 : Litex.In _value_i4 (Litex.Z (M := M)) := h_133
  change Litex.In _value_i4 (Litex.Z (M := M))
  exact h_133));
(Litex.finiteAggregate true _wd_1_0 _wd_1_1 .integer (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i4 : M.Value) => True)) (by
  let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
  _finite_0)) (by
  let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.emptySubset (Litex.Z (M := M))))) (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.integerToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .integer _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))

theorem h_119 : (by
  let _equal_wd_1_0 := (_object_w12 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w12 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) ((show (Litex.denote _equal_wd_1_0) = M.number (1 : ℂ) from (by
          let _aggregate := _equal_wd_1_0
          apply Litex.finiteAggregateListDenote _aggregate [] (1 : ℂ)
          · exact (by
            let _enumerated := (_equal_wd_1_0).val.set
            have _enumeration_same : Litex.Same (_equal_wd_1_0).val.set _enumerated := (show @Eq M.Value _ _ from Eq.refl _)
            let _collection_tail_0 := _enumerated
            have _members_0 : ∀ x, M.mem x (Litex.denote _collection_tail_0) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
            intro x
            exact Eq.mpr (congrArg (fun _set => M.mem x _set ↔ x ∈ ([] : List M.Value)) _enumeration_same) (_members_0 x))
          · norm_num [List.toFinset_cons, List.toFinset_nil]))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))).symm)))
      )
  )

theorem h_259 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_1_0 := _wd_2_0
      let _atomic_wd_1_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0));
  let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => _raw_i5) (by
    intro _raw_i5 h_286 _
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_286)
    have h_286 : Litex.In _value_i5 (Litex.Q (M := M)) := h_286
    change Litex.In _value_i5 (Litex.Q (M := M))
    exact h_286));
  (Litex.finiteAggregate false _wd_1_0 _wd_1_1 .rational (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True)) (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (let _setElement_0 := _wd_2_0;
      let _setElement_1 := _wd_2_1;
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        let _atomic_wd_2_1 := _wd_2_1
        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0))
    exact (let _finite_tail_0 := _atomic_wd_1_0;
    let _finite_tail_1 := _finite_tail_0.val.tail;
    let _finite_tail_2 := _finite_tail_1.val.tail;
    have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
    have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
    _finite_0)) (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (let _setElement_0 := _wd_2_0;
      let _setElement_1 := _wd_2_1;
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        let _atomic_wd_2_1 := _wd_2_1
        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0))
    exact (by
      let _set := _atomic_wd_1_0
      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
      let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
      let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M))))))) (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.rationalToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .rational _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))
  let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (let _setElement_0 := _wd_2_0;
          let _setElement_1 := _wd_2_1;
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            let _atomic_wd_1_1 := _wd_2_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0));
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => _raw_i5) (by
          intro _raw_i5 h_286 _
          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_286)
          have h_286 : Litex.In _value_i5 (Litex.Q (M := M)) := h_286
          change Litex.In _value_i5 (Litex.Q (M := M))
          exact h_286));
        (Litex.finiteAggregate false _wd_1_0 _wd_1_1 .rational (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True)) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0)) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M))))))) (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.rationalToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .rational _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)));
        let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) (((Eq.refl (Litex.denote (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (let _setElement_0 := _wd_2_0;
          let _setElement_1 := _wd_2_1;
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            let _atomic_wd_1_1 := _wd_2_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0));
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => _raw_i5) (by
          intro _raw_i5 h_170 _
          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_170)
          have h_170 : Litex.In _value_i5 (Litex.Q (M := M)) := h_170
          change Litex.In _value_i5 (Litex.Q (M := M))
          exact h_170));
        (Litex.finiteAggregate false _wd_1_0 _wd_1_1 .rational (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True)) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0)) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M))))))) (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.rationalToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .rational _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))))).trans (show (Litex.denote (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (let _setElement_0 := _wd_2_0;
          let _setElement_1 := _wd_2_1;
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            let _atomic_wd_1_1 := _wd_2_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0));
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => _raw_i5) (by
          intro _raw_i5 h_170 _
          let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_170)
          have h_170 : Litex.In _value_i5 (Litex.Q (M := M)) := h_170
          change Litex.In _value_i5 (Litex.Q (M := M))
          exact h_170));
        (Litex.finiteAggregate false _wd_1_0 _wd_1_1 .rational (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True)) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0)) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M))))))) (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.rationalToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .rational _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))) = M.number ((5 : ℂ) / (6 : ℂ)) from (by
          let _aggregate := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_1_0 := _wd_2_0
              let _atomic_wd_1_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0));
          let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => _raw_i5) (by
            intro _raw_i5 h_170 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_170)
            have h_170 : Litex.In _value_i5 (Litex.Q (M := M)) := h_170
            change Litex.In _value_i5 (Litex.Q (M := M))
            exact h_170));
          (Litex.finiteAggregate false _wd_1_0 _wd_1_1 .rational (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True)) (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            (let _setElement_0 := _wd_2_0;
              let _setElement_1 := _wd_2_1;
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                let _atomic_wd_2_0 := _wd_2_0
                let _atomic_wd_2_1 := _wd_2_1
                exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            exact (let _finite_tail_0 := _atomic_wd_1_0;
            let _finite_tail_1 := _finite_tail_0.val.tail;
            let _finite_tail_2 := _finite_tail_1.val.tail;
            have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
            have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
            have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
            _finite_0)) (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            (let _setElement_0 := _wd_2_0;
              let _setElement_1 := _wd_2_1;
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                let _atomic_wd_2_0 := _wd_2_0
                let _atomic_wd_2_1 := _wd_2_1
                exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            exact (by
              let _set := _atomic_wd_1_0
              exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
              let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
              let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M))))))) (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.rationalToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .rational _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number ((1 : ℂ) / (3 : ℂ)))) = ((1 : ℂ) / (3 : ℂ)) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => _raw_i5) (by
            intro _raw_i5 h_226 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_226)
            have h_226 : Litex.In _value_i5 (Litex.Q (M := M)) := h_226
            change Litex.In _value_i5 (Litex.Q (M := M))
            exact h_226));
          let _object_w15 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True) _wd_1_0 _object_w15 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w15
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_object_w15).wd.1 (_object_w15).wd.2.1 (_object_w15).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => _raw_i5) (by
            intro _raw_i5 h_226 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_226)
            have h_226 : Litex.In _value_i5 (Litex.Q (M := M)) := h_226
            change Litex.In _value_i5 (Litex.Q (M := M))
            exact h_226))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) := rfl
            have _calculated : (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number ((1 : ℂ) / (3 : ℂ)) := (show (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number ((1 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.divValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.div_numbers (1 : ℂ) (3 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))
            have _argument : Litex.denote _call.val.argument = M.number ((1 : ℂ) / (3 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((1 : ℂ) / (3 : ℂ))))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number ((1 : ℂ) / (3 : ℂ)))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number ((1 : ℂ) / (2 : ℂ)))) = ((1 : ℂ) / (2 : ℂ)) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => _raw_i5) (by
            intro _raw_i5 h_249 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_249)
            have h_249 : Litex.In _value_i5 (Litex.Q (M := M)) := h_249
            change Litex.In _value_i5 (Litex.Q (M := M))
            exact h_249));
          let _object_w17 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True) _wd_1_0 _object_w17 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w17
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w17).wd.1 (_object_w17).wd.2.1 (_object_w17).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => _raw_i5) (by
            intro _raw_i5 h_249 _
            let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_249)
            have h_249 : Litex.In _value_i5 (Litex.Q (M := M)) := h_249
            change Litex.In _value_i5 (Litex.Q (M := M))
            exact h_249))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i5 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) := rfl
            have _calculated : (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number ((1 : ℂ) / (2 : ℂ)) := (show (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number ((1 : ℂ) / (2 : ℂ)) from ((congrArg₂ M.divValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((M.div_numbers (1 : ℂ) (2 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))
            have _argument : Litex.denote _call.val.argument = M.number ((1 : ℂ) / (2 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number ((1 : ℂ) / (2 : ℂ)))
          apply Litex.finiteAggregateListDenote _aggregate [((1 : ℂ) / (3 : ℂ)), ((1 : ℂ) / (2 : ℂ))] ((5 : ℂ) / (6 : ℂ))
          · exact (by
            let _enumerated := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            (let _setElement_0 := _wd_1_0;
              let _setElement_1 := _wd_1_1;
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                let _atomic_wd_1_1 := _wd_1_1
                exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            have _enumeration_same : Litex.Same (let _wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            (let _setElement_0 := _wd_1_0;
              let _setElement_1 := _wd_1_1;
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                let _atomic_wd_1_1 := _wd_1_1
                exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)) _enumerated := (show @Eq M.Value _ _ from Eq.refl _)
            let _collection_tail_0 := _enumerated
            let _collection_tail_1 := _collection_tail_0.val.tail
            let _collection_tail_2 := _collection_tail_1.val.tail
            have _members_2 : ∀ x, M.mem x (Litex.denote _collection_tail_2) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
            have _number_1 : Litex.denote _collection_tail_1.val.element = M.number ((1 : ℂ) / (2 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))
            have _members_1 := Litex.finiteMembersInsert _collection_tail_1 (M.number ((1 : ℂ) / (2 : ℂ))) [] _number_1 _members_2
            have _number_0 : Litex.denote _collection_tail_0.val.element = M.number ((1 : ℂ) / (3 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((1 : ℂ) / (3 : ℂ))))
            have _members_0 := Litex.finiteMembersInsert _collection_tail_0 (M.number ((1 : ℂ) / (3 : ℂ))) [M.number ((1 : ℂ) / (2 : ℂ))] _number_0 _members_1
            intro x
            exact Eq.mpr (congrArg (fun _set => M.mem x _set ↔ x ∈ ([M.number ((1 : ℂ) / (3 : ℂ)), M.number ((1 : ℂ) / (2 : ℂ))] : List M.Value)) _enumeration_same) (_members_0 x))
          · norm_num [List.toFinset_cons, List.toFinset_nil, _aggregate_term_0, _aggregate_term_1]))))).trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : ((5 : ℂ) / (6 : ℂ)) = ((5 : ℂ) / (6 : ℂ))))).symm)))
      )
  )

noncomputable def _object_w26 := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(let _setElement_0 := _wd_2_0;
  let _setElement_1 := _wd_2_1;
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    let _atomic_wd_1_1 := _wd_2_1
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0));
let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => _raw_i6) (by
  intro _raw_i6 h_359 _
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_359)
  have h_359 : Litex.In _value_i6 (Litex.Q (M := M)) := h_359
  change Litex.In _value_i6 (Litex.Q (M := M))
  exact h_359));
(Litex.finiteAggregate false _wd_1_0 _wd_1_1 .rational (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i6 : M.Value) => True)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      let _atomic_wd_2_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      let _atomic_wd_2_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
    let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
    let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M))))))) (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.rationalToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .rational _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))

theorem h_332 : (by
  let _equal_wd_1_0 := (_object_w26 (M := M))
  let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w26 (M := M));
        let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) ((show (Litex.denote _equal_wd_1_0) = M.number ((5 : ℂ) / (6 : ℂ)) from (by
          let _aggregate := _equal_wd_1_0
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number ((1 : ℂ) / (3 : ℂ)))) = ((1 : ℂ) / (3 : ℂ)) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => _raw_i6) (by
            intro _raw_i6 h_417 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_417)
            have h_417 : Litex.In _value_i6 (Litex.Q (M := M)) := h_417
            change Litex.In _value_i6 (Litex.Q (M := M))
            exact h_417));
          let _object_w23 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i6 : M.Value) => True) _wd_1_0 _object_w23 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w23
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_object_w23).wd.1 (_object_w23).wd.2.1 (_object_w23).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i6 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) := rfl
            have _calculated : (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number ((1 : ℂ) / (3 : ℂ)) := (show (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number ((1 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.divValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.div_numbers (1 : ℂ) (3 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))
            have _argument : Litex.denote _call.val.argument = M.number ((1 : ℂ) / (3 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((1 : ℂ) / (3 : ℂ))))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number ((1 : ℂ) / (3 : ℂ)))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number ((1 : ℂ) / (2 : ℂ)))) = ((1 : ℂ) / (2 : ℂ)) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => _raw_i6) (by
            intro _raw_i6 h_440 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_440)
            have h_440 : Litex.In _value_i6 (Litex.Q (M := M)) := h_440
            change Litex.In _value_i6 (Litex.Q (M := M))
            exact h_440));
          let _object_w25 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i6 : M.Value) => True) _wd_1_0 _object_w25 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w25
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w25).wd.1 (_object_w25).wd.2.1 (_object_w25).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i6 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) := rfl
            have _calculated : (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number ((1 : ℂ) / (2 : ℂ)) := (show (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number ((1 : ℂ) / (2 : ℂ)) from ((congrArg₂ M.divValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((M.div_numbers (1 : ℂ) (2 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))
            have _argument : Litex.denote _call.val.argument = M.number ((1 : ℂ) / (2 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number ((1 : ℂ) / (2 : ℂ)))
          apply Litex.finiteAggregateListDenote _aggregate [((1 : ℂ) / (3 : ℂ)), ((1 : ℂ) / (2 : ℂ))] ((5 : ℂ) / (6 : ℂ))
          · exact (by
            let _enumerated := (_equal_wd_1_0).val.set
            have _enumeration_same : Litex.Same (_equal_wd_1_0).val.set _enumerated := (show @Eq M.Value _ _ from Eq.refl _)
            let _collection_tail_0 := _enumerated
            let _collection_tail_1 := _collection_tail_0.val.tail
            let _collection_tail_2 := _collection_tail_1.val.tail
            have _members_2 : ∀ x, M.mem x (Litex.denote _collection_tail_2) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
            have _number_1 : Litex.denote _collection_tail_1.val.element = M.number ((1 : ℂ) / (2 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))
            have _members_1 := Litex.finiteMembersInsert _collection_tail_1 (M.number ((1 : ℂ) / (2 : ℂ))) [] _number_1 _members_2
            have _number_0 : Litex.denote _collection_tail_0.val.element = M.number ((1 : ℂ) / (3 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((1 : ℂ) / (3 : ℂ))))
            have _members_0 := Litex.finiteMembersInsert _collection_tail_0 (M.number ((1 : ℂ) / (3 : ℂ))) [M.number ((1 : ℂ) / (2 : ℂ))] _number_0 _members_1
            intro x
            exact Eq.mpr (congrArg (fun _set => M.mem x _set ↔ x ∈ ([M.number ((1 : ℂ) / (3 : ℂ)), M.number ((1 : ℂ) / (2 : ℂ))] : List M.Value)) _enumeration_same) (_members_0 x))
          · norm_num [List.toFinset_cons, List.toFinset_nil, _aggregate_term_0, _aggregate_term_1]))))).trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : ((5 : ℂ) / (6 : ℂ)) = ((5 : ℂ) / (6 : ℂ))))).symm)))
      )
  )

theorem h_565 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_1_0 := _wd_2_0
      let _atomic_wd_1_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0));
  let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
    intro _raw_i7 h_592 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_592)
    have h_592 : Litex.In _value_i7 (Litex.Q (M := M)) := h_592
    change Litex.In _value_i7 (Litex.Q (M := M))
    exact h_592));
  (Litex.finiteAggregate true _wd_1_0 _wd_1_1 .rational (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True)) (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (let _setElement_0 := _wd_2_0;
      let _setElement_1 := _wd_2_1;
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        let _atomic_wd_2_1 := _wd_2_1
        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0))
    exact (let _finite_tail_0 := _atomic_wd_1_0;
    let _finite_tail_1 := _finite_tail_0.val.tail;
    let _finite_tail_2 := _finite_tail_1.val.tail;
    have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
    have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
    _finite_0)) (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (let _setElement_0 := _wd_2_0;
      let _setElement_1 := _wd_2_1;
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        let _atomic_wd_2_1 := _wd_2_1
        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0))
    exact (by
      let _set := _atomic_wd_1_0
      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
      let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
      let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M))))))) (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.rationalToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .rational _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))
  let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (let _setElement_0 := _wd_2_0;
          let _setElement_1 := _wd_2_1;
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            let _atomic_wd_1_1 := _wd_2_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0));
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
          intro _raw_i7 h_592 _
          let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_592)
          have h_592 : Litex.In _value_i7 (Litex.Q (M := M)) := h_592
          change Litex.In _value_i7 (Litex.Q (M := M))
          exact h_592));
        (Litex.finiteAggregate true _wd_1_0 _wd_1_1 .rational (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True)) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0)) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M))))))) (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.rationalToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .rational _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)));
        let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) (((Eq.refl (Litex.denote (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (let _setElement_0 := _wd_2_0;
          let _setElement_1 := _wd_2_1;
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            let _atomic_wd_1_1 := _wd_2_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0));
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
          intro _raw_i7 h_476 _
          let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_476)
          have h_476 : Litex.In _value_i7 (Litex.Q (M := M)) := h_476
          change Litex.In _value_i7 (Litex.Q (M := M))
          exact h_476));
        (Litex.finiteAggregate true _wd_1_0 _wd_1_1 .rational (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True)) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0)) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M))))))) (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.rationalToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .rational _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))))).trans (show (Litex.denote (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (let _setElement_0 := _wd_2_0;
          let _setElement_1 := _wd_2_1;
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            let _atomic_wd_1_1 := _wd_2_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0));
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
          intro _raw_i7 h_476 _
          let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_476)
          have h_476 : Litex.In _value_i7 (Litex.Q (M := M)) := h_476
          change Litex.In _value_i7 (Litex.Q (M := M))
          exact h_476));
        (Litex.finiteAggregate true _wd_1_0 _wd_1_1 .rational (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True)) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0)) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M))))))) (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.rationalToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .rational _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))) = M.number ((1 : ℂ) / (6 : ℂ)) from (by
          let _aggregate := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_1_0 := _wd_2_0
              let _atomic_wd_1_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0));
          let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
            intro _raw_i7 h_476 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_476)
            have h_476 : Litex.In _value_i7 (Litex.Q (M := M)) := h_476
            change Litex.In _value_i7 (Litex.Q (M := M))
            exact h_476));
          (Litex.finiteAggregate true _wd_1_0 _wd_1_1 .rational (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True)) (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            (let _setElement_0 := _wd_2_0;
              let _setElement_1 := _wd_2_1;
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                let _atomic_wd_2_0 := _wd_2_0
                let _atomic_wd_2_1 := _wd_2_1
                exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            exact (let _finite_tail_0 := _atomic_wd_1_0;
            let _finite_tail_1 := _finite_tail_0.val.tail;
            let _finite_tail_2 := _finite_tail_1.val.tail;
            have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
            have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
            have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
            _finite_0)) (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            (let _setElement_0 := _wd_2_0;
              let _setElement_1 := _wd_2_1;
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                let _atomic_wd_2_0 := _wd_2_0
                let _atomic_wd_2_1 := _wd_2_1
                exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            exact (by
              let _set := _atomic_wd_1_0
              exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
              let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
              let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M))))))) (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.rationalToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .rational _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number ((1 : ℂ) / (3 : ℂ)))) = ((1 : ℂ) / (3 : ℂ)) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
            intro _raw_i7 h_532 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_532)
            have h_532 : Litex.In _value_i7 (Litex.Q (M := M)) := h_532
            change Litex.In _value_i7 (Litex.Q (M := M))
            exact h_532));
          let _object_w29 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True) _wd_1_0 _object_w29 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w29
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_object_w29).wd.1 (_object_w29).wd.2.1 (_object_w29).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
            intro _raw_i7 h_532 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_532)
            have h_532 : Litex.In _value_i7 (Litex.Q (M := M)) := h_532
            change Litex.In _value_i7 (Litex.Q (M := M))
            exact h_532))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) := rfl
            have _calculated : (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number ((1 : ℂ) / (3 : ℂ)) := (show (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number ((1 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.divValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.div_numbers (1 : ℂ) (3 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))
            have _argument : Litex.denote _call.val.argument = M.number ((1 : ℂ) / (3 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((1 : ℂ) / (3 : ℂ))))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number ((1 : ℂ) / (3 : ℂ)))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number ((1 : ℂ) / (2 : ℂ)))) = ((1 : ℂ) / (2 : ℂ)) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
            intro _raw_i7 h_555 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_555)
            have h_555 : Litex.In _value_i7 (Litex.Q (M := M)) := h_555
            change Litex.In _value_i7 (Litex.Q (M := M))
            exact h_555));
          let _object_w31 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True) _wd_1_0 _object_w31 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w31
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w31).wd.1 (_object_w31).wd.2.1 (_object_w31).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => _raw_i7) (by
            intro _raw_i7 h_555 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_555)
            have h_555 : Litex.In _value_i7 (Litex.Q (M := M)) := h_555
            change Litex.In _value_i7 (Litex.Q (M := M))
            exact h_555))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i7 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) := rfl
            have _calculated : (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number ((1 : ℂ) / (2 : ℂ)) := (show (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number ((1 : ℂ) / (2 : ℂ)) from ((congrArg₂ M.divValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((M.div_numbers (1 : ℂ) (2 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))
            have _argument : Litex.denote _call.val.argument = M.number ((1 : ℂ) / (2 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number ((1 : ℂ) / (2 : ℂ)))
          apply Litex.finiteAggregateListDenote _aggregate [((1 : ℂ) / (3 : ℂ)), ((1 : ℂ) / (2 : ℂ))] ((1 : ℂ) / (6 : ℂ))
          · exact (by
            let _enumerated := ((_object_w26 (M := M))).val.set
            have _enumeration_same : Litex.Same ((_object_w26 (M := M))).val.set _enumerated := (show @Eq M.Value _ _ from Eq.refl _)
            let _collection_tail_0 := _enumerated
            let _collection_tail_1 := _collection_tail_0.val.tail
            let _collection_tail_2 := _collection_tail_1.val.tail
            have _members_2 : ∀ x, M.mem x (Litex.denote _collection_tail_2) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
            have _number_1 : Litex.denote _collection_tail_1.val.element = M.number ((1 : ℂ) / (2 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))
            have _members_1 := Litex.finiteMembersInsert _collection_tail_1 (M.number ((1 : ℂ) / (2 : ℂ))) [] _number_1 _members_2
            have _number_0 : Litex.denote _collection_tail_0.val.element = M.number ((1 : ℂ) / (3 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((1 : ℂ) / (3 : ℂ))))
            have _members_0 := Litex.finiteMembersInsert _collection_tail_0 (M.number ((1 : ℂ) / (3 : ℂ))) [M.number ((1 : ℂ) / (2 : ℂ))] _number_0 _members_1
            intro x
            exact Eq.mpr (congrArg (fun _set => M.mem x _set ↔ x ∈ ([M.number ((1 : ℂ) / (3 : ℂ)), M.number ((1 : ℂ) / (2 : ℂ))] : List M.Value)) _enumeration_same) (_members_0 x))
          · norm_num [List.toFinset_cons, List.toFinset_nil, _aggregate_term_0, _aggregate_term_1]))))).trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (6 : ℂ)) = ((1 : ℂ) / (6 : ℂ))))).symm)))
      )
  )

noncomputable def _object_w40 := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(let _setElement_0 := _wd_2_0;
  let _setElement_1 := _wd_2_1;
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    let _atomic_wd_1_1 := _wd_2_1
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0));
let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => True) (fun (_raw_i8 : M.Value) => _raw_i8) (by
  intro _raw_i8 h_665 _
  let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_665)
  have h_665 : Litex.In _value_i8 (Litex.Q (M := M)) := h_665
  change Litex.In _value_i8 (Litex.Q (M := M))
  exact h_665));
(Litex.finiteAggregate true _wd_1_0 _wd_1_1 .rational (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => True)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      let _atomic_wd_2_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      let _atomic_wd_2_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
    let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
    let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M))))))) (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.rationalToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .rational _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)))

theorem h_638 : (by
  let _equal_wd_1_0 := (_object_w40 (M := M))
  let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w40 (M := M));
        let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.denote _equal_wd_1_0) from rfl) ((show (Litex.denote _equal_wd_1_0) = M.number ((1 : ℂ) / (6 : ℂ)) from (by
          let _aggregate := _equal_wd_1_0
          have _aggregate_term_0 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number ((1 : ℂ) / (3 : ℂ)))) = ((1 : ℂ) / (3 : ℂ)) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => True) (fun (_raw_i8 : M.Value) => _raw_i8) (by
            intro _raw_i8 h_723 _
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_723)
            have h_723 : Litex.In _value_i8 (Litex.Q (M := M)) := h_723
            change Litex.In _value_i8 (Litex.Q (M := M))
            exact h_723));
          let _object_w37 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => True) _wd_1_0 _object_w37 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w37
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_object_w37).wd.1 (_object_w37).wd.2.1 (_object_w37).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) := rfl
            have _calculated : (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number ((1 : ℂ) / (3 : ℂ)) := (show (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number ((1 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.divValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.div_numbers (1 : ℂ) (3 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))
            have _argument : Litex.denote _call.val.argument = M.number ((1 : ℂ) / (3 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((1 : ℂ) / (3 : ℂ))))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number ((1 : ℂ) / (3 : ℂ)))
          have _aggregate_term_1 : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number ((1 : ℂ) / (2 : ℂ)))) = ((1 : ℂ) / (2 : ℂ)) := (congrArg (Litex.NativeBridge.complexValue (M := M)) (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => True) (fun (_raw_i8 : M.Value) => _raw_i8) (by
            intro _raw_i8 h_746 _
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_746)
            have h_746 : Litex.In _value_i8 (Litex.Q (M := M)) := h_746
            change Litex.In _value_i8 (Litex.Q (M := M))
            exact h_746));
          let _object_w39 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => True) _wd_1_0 _object_w39 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w39
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w39).wd.1 (_object_w39).wd.2.1 (_object_w39).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i8 : M.Value) => True) _).mpr _call.wd.2)
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) := rfl
            have _calculated : (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number ((1 : ℂ) / (2 : ℂ)) := (show (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number ((1 : ℂ) / (2 : ℂ)) from ((congrArg₂ M.divValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((M.div_numbers (1 : ℂ) (2 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))
            have _argument : Litex.denote _call.val.argument = M.number ((1 : ℂ) / (2 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))).trans (Litex.NativeBridge.complexValue_number ((1 : ℂ) / (2 : ℂ)))
          apply Litex.finiteAggregateListDenote _aggregate [((1 : ℂ) / (3 : ℂ)), ((1 : ℂ) / (2 : ℂ))] ((1 : ℂ) / (6 : ℂ))
          · exact (by
            let _enumerated := (_equal_wd_1_0).val.set
            have _enumeration_same : Litex.Same (_equal_wd_1_0).val.set _enumerated := (show @Eq M.Value _ _ from Eq.refl _)
            let _collection_tail_0 := _enumerated
            let _collection_tail_1 := _collection_tail_0.val.tail
            let _collection_tail_2 := _collection_tail_1.val.tail
            have _members_2 : ∀ x, M.mem x (Litex.denote _collection_tail_2) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
            have _number_1 : Litex.denote _collection_tail_1.val.element = M.number ((1 : ℂ) / (2 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))
            have _members_1 := Litex.finiteMembersInsert _collection_tail_1 (M.number ((1 : ℂ) / (2 : ℂ))) [] _number_1 _members_2
            have _number_0 : Litex.denote _collection_tail_0.val.element = M.number ((1 : ℂ) / (3 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((1 : ℂ) / (3 : ℂ))))
            have _members_0 := Litex.finiteMembersInsert _collection_tail_0 (M.number ((1 : ℂ) / (3 : ℂ))) [M.number ((1 : ℂ) / (2 : ℂ))] _number_0 _members_1
            intro x
            exact Eq.mpr (congrArg (fun _set => M.mem x _set ↔ x ∈ ([M.number ((1 : ℂ) / (3 : ℂ)), M.number ((1 : ℂ) / (2 : ℂ))] : List M.Value)) _enumeration_same) (_members_0 x))
          · norm_num [List.toFinset_cons, List.toFinset_nil, _aggregate_term_0, _aggregate_term_1]))))).trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (6 : ℂ)) = ((1 : ℂ) / (6 : ℂ))))).symm)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_finite_x5f_aggregates_x2f_statement_x2e_lit
