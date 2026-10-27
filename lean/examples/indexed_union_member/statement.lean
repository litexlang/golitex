import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_indexed_x5f_union_x5f_member_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.IsNonempty _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_7 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_9 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_8 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
    have h_8 : Litex.In _value_i4 _value_i1 := h_8
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_10 : Litex.In _value_i5 _value_i1) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_18 : Litex.In _value_i6 (let _litex_call_arg_0 := _value_i5;
Litex.callOnDomain _value_i1 (Litex.powerSet _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_9 h_10 True.intro)), (by
  let _object_w3 := (Litex.indexUnion _value_i1 _value_i2 _value_i3 h_6 (Litex.isSet _value_i1) h_7 (by
    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _value_i1) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → True := (by
        intro _raw_i7 h_31 _
        let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_31)
        have h_31 : Litex.In _value_i7 _value_i1 := h_31
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)))
    exact (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
        intro _raw_i4 h_8 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
        have h_8 : Litex.In _value_i4 _value_i1 := h_8
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
        intro _raw_i4 h_8 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
        have h_8 : Litex.In _value_i4 _value_i1 := h_8
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_9)))
  exact (by
    let _atomic_wd_1_1 := _object_w3
    exact Litex.In _value_i6 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_7 _Host_i3 _rep_i3 _value_i3 h_9 _Host_i5 _rep_i5 _value_i5 h_10 _Host_i6 _rep_i6 _value_i6 h_18
          let _object_w3 := (Litex.indexUnion _value_i1 _value_i2 _value_i3 h_6 (Litex.isSet _value_i1) h_7 (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i7 : M.Value), M.mem _raw_i7 (Litex.denote _value_i1) → ((fun (_raw_i7 : M.Value) => True) _raw_i7) → True := (by
                intro _raw_i7 h_31 _
                let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_31)
                have h_31 : Litex.In _value_i7 _value_i1 := h_31
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input)))
            exact (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                intro _raw_i4 h_8 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
                have h_8 : Litex.In _value_i4 _value_i1 := h_8
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                intro _raw_i4 h_8 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
                have h_8 : Litex.In _value_i4 _value_i1 := h_8
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_9)))
          have h_1 : (by
            let _atomic_wd_1_1 := _object_w3
            exact Litex.In _value_i6 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w3
                    exact (Litex.indexUnionMember _atomic_wd_1_1 _value_i5 _value_i6 h_10 (by
                      let _atomic_wd_2_1 := (let _litex_call_arg_0 := _value_i5;
                      Litex.callOnDomain _value_i1 (Litex.powerSet _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_9 h_10 True.intro)
                      exact h_18)))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_indexed_x5f_union_x5f_member_x2f_statement_x2e_lit
