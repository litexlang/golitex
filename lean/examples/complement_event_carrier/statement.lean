import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_complement_x5f_event_x5f_carrier_x2f_statement_x2e_lit

universe u v1 v2 v4 v5 v6 v7 v8 v9
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_8 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote (Litex.powerSet _value_i1)) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_6 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6)
    have h_6 : Litex.In _value_i3 (Litex.powerSet _value_i1) := h_6
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.powerSet _value_i1)) (Litex.denote _litex_output) (Litex.isSet (Litex.powerSet _value_i1)) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_9 : Litex.IsSet _value_i4) (h_1 : (by
  let _atomic_wd_1_0 := (let _object_w3 := (Litex.setMinus _value_i1 _value_i4);
  (let _litex_call_arg_0 := _object_w3;
  Litex.callOnDomain (Litex.powerSet _value_i1) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_8 (by
    let _atomic_wd_2_0 := _object_w3
    let _atomic_wd_2_1 := (Litex.powerSet _value_i1)
    exact ((Litex.inPowerSet_iff _atomic_wd_2_0 _value_i1).mpr (Litex.setMinusSubsetOfLeft _value_i1 _value_i4 _value_i1 (Litex.subsetOfSame _value_i1 _value_i1 _value_i1 _value_i1 rfl (show @Eq M.Value _ _ from Eq.refl _) (Litex.subsetRefl _value_i1))))) True.intro))
  exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0)), (by
  let _atomic_wd_1_0 := (let _object_w4 := (Litex.setMinus _value_i1 _value_i4);
  (let _litex_call_arg_0 := _object_w4;
  Litex.callOnDomain (Litex.powerSet _value_i1) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_8 (by
    let _atomic_wd_1_0 := _object_w4
    let _atomic_wd_1_1 := (Litex.powerSet _value_i1)
    exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i1).mpr (Litex.setMinusSubsetOfLeft _value_i1 _value_i4 _value_i1 (Litex.subsetOfSame _value_i1 _value_i1 _value_i1 _value_i1 rfl (show @Eq M.Value _ _ from Eq.refl _) (Litex.subsetRefl _value_i1))))) True.intro))
  exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_8 _Host_i4 _rep_i4 _value_i4 h_9 h_1
          have h_2 : (by
            let _atomic_wd_1_0 := (let _object_w4 := (Litex.setMinus _value_i1 _value_i4);
            (let _litex_call_arg_0 := _object_w4;
            Litex.callOnDomain (Litex.powerSet _value_i1) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_8 (by
              let _atomic_wd_1_0 := _object_w4
              let _atomic_wd_1_1 := (Litex.powerSet _value_i1)
              exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i1).mpr (Litex.setMinusSubsetOfLeft _value_i1 _value_i4 _value_i1 (Litex.subsetOfSame _value_i1 _value_i1 _value_i1 _value_i1 rfl (show @Eq M.Value _ _ from Eq.refl _) (Litex.subsetRefl _value_i1))))) True.intro))
            exact Litex.Lt (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _object_w4 := (Litex.setMinus _value_i1 _value_i4);
                    (let _litex_call_arg_0 := _object_w4;
                    Litex.callOnDomain (Litex.powerSet _value_i1) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_8 (by
                      let _atomic_wd_1_0 := _object_w4
                      let _atomic_wd_1_1 := (Litex.powerSet _value_i1)
                      exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i1).mpr (Litex.setMinusSubsetOfLeft _value_i1 _value_i4 _value_i1 (Litex.subsetOfSame _value_i1 _value_i1 _value_i1 _value_i1 rfl (show @Eq M.Value _ _ from Eq.refl _) (Litex.subsetRefl _value_i1))))) True.intro))
                    exact h_1)
                )
            )
          exact h_2
        )
      )
  )

theorem h_66 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_67 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_68 : Litex.IsSet _value_i6), (by
  let _object_w7 := (Litex.setMinus _value_i5 _value_i6)
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
          intro _Host_i5 _rep_i5 _value_i5 h_67 _Host_i6 _rep_i6 _value_i6 h_68
          let _object_w7 := (Litex.setMinus _value_i5 _value_i6)
          let _object_w8 := (Litex.powerSet _value_i5)
          have h_65 : (by
            let _atomic_wd_1_0 := _object_w7
            let _atomic_wd_1_1 := _object_w8
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w7
                    let _atomic_wd_1_1 := _object_w8
                    exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i5).mpr (Litex.setMinusSubsetOfLeft _value_i5 _value_i6 _value_i5 (Litex.subsetOfSame _value_i5 _value_i5 _value_i5 _value_i5 rfl (show @Eq M.Value _ _ from Eq.refl _) (Litex.subsetRefl _value_i5)))))
                )
            )
          exact h_65
        )
      )
  )

theorem h_73 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_74 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_75 : Litex.IsSet _value_i8) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_76 : Litex.IsSet _value_i9) (h_71 : Litex.Same _value_i7 _value_i8), (by
  let _object_w9 := (Litex.setMinus _value_i7 _value_i9)
  let _object_w10 := (Litex.powerSet _value_i8)
  exact (by
    let _atomic_wd_1_0 := _object_w9
    let _atomic_wd_1_1 := _object_w10
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_74 _Host_i8 _rep_i8 _value_i8 h_75 _Host_i9 _rep_i9 _value_i9 h_76 h_71
          let _object_w9 := (Litex.setMinus _value_i7 _value_i9)
          let _object_w10 := (Litex.powerSet _value_i8)
          have h_72 : (by
            let _atomic_wd_1_0 := _object_w9
            let _atomic_wd_1_1 := _object_w10
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    let _atomic_wd_1_1 := _object_w10
                    exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i8).mpr (Litex.setMinusSubsetOfLeft _value_i7 _value_i9 _value_i8 (Litex.subsetOfSame _value_i7 _value_i7 _value_i7 _value_i8 rfl h_71 (Litex.subsetRefl _value_i7)))))
                )
            )
          exact h_72
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_complement_x5f_event_x5f_carrier_x2f_statement_x2e_lit
