import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_distinct_x5f_real_x5f_pair_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i1 _value_i2), (by
  let _object_w2 := (let _setElement_0 := _value_i1;
    let _setElement_1 := _value_i2;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 h_1 (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact ((Litex.In _value_i1 _object_w2) ∧ (Litex.Subset _object_w2 (Litex.R (M := M))))
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 h_1
    let _object_w2 := (let _setElement_0 := _value_i1;
      let _setElement_1 := _value_i2;
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 h_1 (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    have h_2 : Litex.In _value_i1 _object_w2 :=
      (by
        let _set := _object_w2
        exact ((Litex.inInsert_iff _value_i1 _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _))))
    have h_3 : Litex.Subset _object_w2 (Litex.R (M := M)) :=
      (by
        let _set := _object_w2
        exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd h_17 (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.R (M := M)) _set.val.tail.wd h_18 (Litex.emptySubset (Litex.R (M := M))))))
    exact (And.intro h_2 h_3)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_distinct_x5f_real_x5f_pair_x2f_statement_x2e_lit
