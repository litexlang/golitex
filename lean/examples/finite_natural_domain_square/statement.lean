import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_natural_x5f_domain_x5f_square_x2f_statement_x2e_lit

universe u v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.powValue _raw_i2 (M.number (2 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.N (M := M)) := h_14
  have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (Litex.naturalNonnegative _value_i2 h_14)
  change Litex.In (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i2 h_14) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.N (M := M))
  exact (Litex.powStructuralInN (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i2 h_14) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_14 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))))))
theorem h_89 : Litex.In (_object_i1 (M := M)) (by
  have _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.natural) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := by
    intro _raw_i2 h_72 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_72)
    have h_72 : Litex.In _value_i2 (Litex.N (M := M)) := h_72
    have h_73 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (Litex.naturalNonnegative _value_i2 h_72)
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True))) :=
  (Litex.formulaFnInFnSet (_object_i1 (M := M)))
theorem h_90 : Litex.Same (_object_i1 (M := M)) (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.powValue _raw_i2 (M.number (2 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.N (M := M)) := h_14
  have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
    (Litex.naturalNonnegative _value_i2 h_14)
  change Litex.In (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i2 h_14) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.N (M := M))
  exact (Litex.powStructuralInN (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.naturalToReal _value_i2 h_14) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) h_14 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num)))))) :=
  (Litex.sameRefl (_object_i1 (M := M)))

noncomputable def _object_i3 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)
theorem h_95 : Litex.IsSet (_object_i3 (M := M)) :=
  (Litex.isSet (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
theorem h_96 : Litex.Same (_object_i3 (M := M)) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) :=
  (Litex.sameRefl (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))

theorem h_97 : Litex.Subset (_object_i3 (M := M)) (Litex.N (M := M)) :=
  (Litex.subsetOfSame (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0) (Litex.N (M := M)) (_object_i3 (M := M)) (Litex.N (M := M)) ((((Litex.sameRefl (_object_i3 (M := M)))).trans (h_96 (M := M)))).symm (Litex.sameRefl (Litex.N (M := M))) (by
    let _set := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.N (M := M)) _set.wd (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInNOfEq (1 : ℂ) (1 : ℕ) (by norm_num))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.N (M := M)) _set.val.tail.wd (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.N (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.emptySubset (Litex.N (M := M)))))))

theorem h_168 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_182 : Litex.In _value_i6 (_object_i3 (M := M))), Litex.In (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i6 (h_89 (M := M)) ((h_97 (M := M)) (Litex.denote _value_i6) h_182) True.intro) (Litex.N (M := M)) :=
  (by
    intro _Host_i6 _rep_i6 _value_i6 h_182
    have h_167 : Litex.In (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i6 (h_89 (M := M)) ((h_97 (M := M)) (Litex.denote _value_i6) h_182) True.intro) (Litex.N (M := M)) :=
      (Litex.inOfSame (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i6 (h_89 (M := M)) ((h_97 (M := M)) (Litex.denote _value_i6) h_182) True.intro) (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i6 (h_89 (M := M)) ((h_97 (M := M)) (Litex.denote _value_i6) h_182) True.intro) (Litex.N (M := M)) (Litex.N (M := M)) (Litex.sameRefl (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i6 (h_89 (M := M)) ((h_97 (M := M)) (Litex.denote _value_i6) h_182) True.intro)) (Litex.sameRefl (Litex.N (M := M))) (Litex.callInOutput (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i6 (h_89 (M := M)) ((h_97 (M := M)) (Litex.denote _value_i6) h_182) True.intro)))
    have h_227 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i6 (h_89 (M := M)) ((h_97 (M := M)) (Litex.denote _value_i6) h_182) True.intro) :=
      (Litex.naturalNonnegative (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i6 (h_89 (M := M)) ((h_97 (M := M)) (Litex.denote _value_i6) h_182) True.intro) h_167)
    exact h_167
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_natural_x5f_domain_x5f_square_x2f_statement_x2e_lit
