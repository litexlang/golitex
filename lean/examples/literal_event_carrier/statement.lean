import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_literal_x5f_event_x5f_carrier_x2f_statement_x2e_lit

universe u v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote (Litex.powerSet _value_i1)) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_7 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7)
    have h_7 : Litex.In _value_i3 (Litex.powerSet _value_i1) := h_7
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.powerSet _value_i1)) (Litex.denote _litex_output) (Litex.isSet (Litex.powerSet _value_i1)) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_10 : Litex.In _value_i4 _value_i1) (h_1 : (by
  let _atomic_wd_1_0 := (let _object_w3 := (let _setElement_0 := _value_i4;
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (let _litex_call_arg_0 := _object_w3;
  Litex.callOnDomain (Litex.powerSet _value_i1) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_9 (by
    let _atomic_wd_2_0 := _object_w3
    let _atomic_wd_2_1 := (Litex.powerSet _value_i1)
    exact ((Litex.inPowerSet_iff _atomic_wd_2_0 _value_i1).mpr (Litex.insertSubset (_atomic_wd_2_0).val.element (_atomic_wd_2_0).val.tail _value_i1 (_atomic_wd_2_0).wd h_10 (Litex.emptySubset _value_i1)))) True.intro))
  exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0)), (by
  let _atomic_wd_1_0 := (let _object_w4 := (let _setElement_0 := _value_i4;
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (let _litex_call_arg_0 := _object_w4;
  Litex.callOnDomain (Litex.powerSet _value_i1) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_9 (by
    let _atomic_wd_1_0 := _object_w4
    let _atomic_wd_1_1 := (Litex.powerSet _value_i1)
    exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i1).mpr (Litex.insertSubset (_atomic_wd_1_0).val.element (_atomic_wd_1_0).val.tail _value_i1 (_atomic_wd_1_0).wd h_10 (Litex.emptySubset _value_i1)))) True.intro))
  exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_9 _Host_i4 _rep_i4 _value_i4 h_10 h_1
          have h_2 : (by
            let _atomic_wd_1_0 := (let _object_w4 := (let _setElement_0 := _value_i4;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (let _litex_call_arg_0 := _object_w4;
            Litex.callOnDomain (Litex.powerSet _value_i1) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_9 (by
              let _atomic_wd_1_0 := _object_w4
              let _atomic_wd_1_1 := (Litex.powerSet _value_i1)
              exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i1).mpr (Litex.insertSubset (_atomic_wd_1_0).val.element (_atomic_wd_1_0).val.tail _value_i1 (_atomic_wd_1_0).wd h_10 (Litex.emptySubset _value_i1)))) True.intro))
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _object_w4 := (let _setElement_0 := _value_i4;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0);
                    (let _litex_call_arg_0 := _object_w4;
                    Litex.callOnDomain (Litex.powerSet _value_i1) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_9 (by
                      let _atomic_wd_1_0 := _object_w4
                      let _atomic_wd_1_1 := (Litex.powerSet _value_i1)
                      exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i1).mpr (Litex.insertSubset (_atomic_wd_1_0).val.element (_atomic_wd_1_0).val.tail _value_i1 (_atomic_wd_1_0).wd h_10 (Litex.emptySubset _value_i1)))) True.intro))
                    exact h_1)
                )
            )
          exact h_2
        )
      )
  )

theorem h_99 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_101 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_102 : Litex.In _value_i6 _value_i5), (by
  let _object_w7 := (let _setElement_0 := _value_i6;
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  let _object_w8 := (Litex.powerSet _value_i5)
  exact (by
    let _atomic_wd_1_0 := _object_w7
    let _atomic_wd_1_1 := _object_w8
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_101 _Host_i6 _rep_i6 _value_i6 h_102
          let _object_w7 := (let _setElement_0 := _value_i6;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          let _object_w8 := (Litex.powerSet _value_i5)
          have h_98 : (by
            let _atomic_wd_1_0 := _object_w7
            let _atomic_wd_1_1 := _object_w8
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w7
                    let _atomic_wd_1_1 := _object_w8
                    exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i5).mpr (Litex.insertSubset (_atomic_wd_1_0).val.element (_atomic_wd_1_0).val.tail _value_i5 (_atomic_wd_1_0).wd h_102 (Litex.emptySubset _value_i5))))
                )
            )
          exact h_98
        )
      )
  )

theorem h_113 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_115 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_116 : Litex.In _value_i8 _value_i7) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_117 : Litex.In _value_i9 _value_i7) (h_111 : ¬ Litex.Same _value_i8 _value_i9), (by
  let _object_w9 := (let _setElement_0 := _value_i8;
    let _setElement_1 := _value_i9;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 h_111 (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  let _object_w10 := (Litex.powerSet _value_i7)
  exact (by
    let _atomic_wd_1_0 := _object_w9
    let _atomic_wd_1_1 := _object_w10
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_115 _Host_i8 _rep_i8 _value_i8 h_116 _Host_i9 _rep_i9 _value_i9 h_117 h_111
          let _object_w9 := (let _setElement_0 := _value_i8;
            let _setElement_1 := _value_i9;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 h_111 (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          let _object_w10 := (Litex.powerSet _value_i7)
          have h_112 : (by
            let _atomic_wd_1_0 := _object_w9
            let _atomic_wd_1_1 := _object_w10
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    let _atomic_wd_1_1 := _object_w10
                    exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i7).mpr (Litex.insertSubset (_atomic_wd_1_0).val.element (_atomic_wd_1_0).val.tail _value_i7 (_atomic_wd_1_0).wd h_116 (Litex.insertSubset ((_atomic_wd_1_0).val.tail).val.element ((_atomic_wd_1_0).val.tail).val.tail _value_i7 ((_atomic_wd_1_0).val.tail).wd h_117 (Litex.emptySubset _value_i7)))))
                )
            )
          exact h_112
        )
      )
  )

theorem h_141 : ∀ {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_143 : Litex.IsSet _value_i10) {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_144 : Litex.IsSet _value_i11) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_145 : Litex.In _value_i12 _value_i10) (h_139 : Litex.Same _value_i10 _value_i11), (by
  let _object_w11 := (let _setElement_0 := _value_i12;
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  let _object_w12 := (Litex.powerSet _value_i11)
  exact (by
    let _atomic_wd_1_0 := _object_w11
    let _atomic_wd_1_1 := _object_w12
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_143 _Host_i11 _rep_i11 _value_i11 h_144 _Host_i12 _rep_i12 _value_i12 h_145 h_139
          let _object_w11 := (let _setElement_0 := _value_i12;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          let _object_w12 := (Litex.powerSet _value_i11)
          have h_140 : (by
            let _atomic_wd_1_0 := _object_w11
            let _atomic_wd_1_1 := _object_w12
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w11
                    let _atomic_wd_1_1 := _object_w12
                    exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i11).mpr (Litex.insertSubset (_atomic_wd_1_0).val.element (_atomic_wd_1_0).val.tail _value_i11 (_atomic_wd_1_0).wd (Litex.inOfSame _value_i12 _value_i12 _value_i10 _value_i11 (show @Eq M.Value _ _ from Eq.refl _) h_139 h_145) (Litex.emptySubset _value_i11))))
                )
            )
          exact h_140
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_literal_x5f_event_x5f_carrier_x2f_statement_x2e_lit
