import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_indexed_x5f_intersection_x5f_member_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.IsNonempty _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_8 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_7 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_7)
    have h_7 : Litex.In _value_i4 _value_i1 := h_7
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_9 : Litex.In _value_i5 _value_i2) (h_2 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_10 : Litex.In _value_i6 _value_i1), (by
  let _atomic_wd_1_1 := (let _litex_call_arg_0 := _value_i6;
  Litex.callOnDomain _value_i1 (Litex.powerSet _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_8 h_10 True.intro)
  exact Litex.In _value_i5 _atomic_wd_1_1)), (by
  let _atomic_wd_1_1 := (Litex.indexIntersect _value_i1 _value_i2 _value_i3 h_5 (Litex.isSet _value_i1) h_6 (by
    let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote _value_i1) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → True := (by
        intro _raw_i8 h_32 _
        let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_32)
        have h_32 : Litex.In _value_i8 _value_i1 := h_32
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)))
    exact (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
        intro _raw_i4 h_7 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_7)
        have h_7 : Litex.In _value_i4 _value_i1 := h_7
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
        intro _raw_i4 h_7 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_7)
        have h_7 : Litex.In _value_i4 _value_i1 := h_7
        exact True.intro);
      Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
      exact (show Litex.Same _left _right from rfl)) h_8)))
  exact Litex.In _value_i5 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_6 _Host_i3 _rep_i3 _value_i3 h_8 _Host_i5 _rep_i5 _value_i5 h_9 h_2
          have h_40 : Litex.IsNonempty _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          have h_41 : Litex.IsSet _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_43 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_42 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_42)
              have h_42 : Litex.In _value_i4 _value_i1 := h_42
              exact True.intro);
            Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_44 : Litex.In _value_i5 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_55 : Litex.In _value_i5 (Litex.indexIntersect _value_i1 _value_i2 _value_i3 h_40 (Litex.isSet _value_i1) h_41 (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _value_i1) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → True := (by
                intro _raw_i11 h_114 _
                let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_114)
                have h_114 : Litex.In _value_i11 _value_i1 := h_114
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)))
            exact (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                intro _raw_i4 h_42 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_42)
                have h_42 : Litex.In _value_i4 _value_i1 := h_42
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                intro _raw_i4 h_42 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_42)
                have h_42 : Litex.In _value_i4 _value_i1 := h_42
                exact True.intro);
              Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_43))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_58 : Litex.In _value_i5 _value_i2 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_44
                          )
                      )
                    have h_57 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_66 : Litex.In _value_i9 _value_i1), Litex.In _value_i5 (let _litex_call_arg_0 := _value_i9;
                    Litex.callOnDomain _value_i1 (Litex.powerSet _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_43 h_66 True.intro) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i9 _rep_i9 _value_i9 h_66
                              exact (h_2 _value_i9 h_66)
                            )
                          )
                      )
                    exact (Litex.indexIntersectMember (Litex.indexIntersect _value_i1 _value_i2 _value_i3 h_40 (Litex.isSet _value_i1) h_41 (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _value_i1) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
                        intro _raw_i10 h_90 _
                        let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_90)
                        have h_90 : Litex.In _value_i10 _value_i1 := h_90
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)))
                    exact (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_42 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_42)
                        have h_42 : Litex.In _value_i4 _value_i1 := h_42
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_42 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_42)
                        have h_42 : Litex.In _value_i4 _value_i1 := h_42
                        exact True.intro);
                      Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
                      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) h_43))) _value_i5 h_58 (Litex.forallMembersOfRepresentations _value_i1 h_57))
                  )
                )
            )
          exact (by
            let _atomic_wd_1_1 := (Litex.indexIntersect _value_i1 _value_i2 _value_i3 h_40 (Litex.isSet _value_i1) h_41 (by
              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote _value_i1) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → True := (by
                  intro _raw_i11 h_114 _
                  let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_114)
                  have h_114 : Litex.In _value_i11 _value_i1 := h_114
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)))
              exact (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_42 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_42)
                  have h_42 : Litex.In _value_i4 _value_i1 := h_42
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_42 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_42)
                  have h_42 : Litex.In _value_i4 _value_i1 := h_42
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.powerSet _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                exact (show Litex.Same _left _right from rfl)) h_43)))
            exact h_55)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_indexed_x5f_intersection_x5f_member_x2f_statement_x2e_lit
