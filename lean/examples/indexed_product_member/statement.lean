import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_indexed_x5f_product_x5f_member_x2f_statement_x2e_lit

universe u v1 v2 v3 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]
variable [_indexedUnionSemantics : Litex.IndexedUnionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.IsNonempty _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_5 : Litex.IsNonempty _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_7 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_6 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_6)
    have h_6 : Litex.In _value_i4 _value_i1 := h_6
    exact True.intro);
  Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_9 : Litex.In _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _value_i1) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
    intro _raw_i6 h_8 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_8)
    have h_8 : Litex.In _value_i6 _value_i1 := h_8
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.familyUnion _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)))) (h_1 : Litex.IsChoiceFunctionFor _value_i1 _value_i2 _value_i3 _value_i5), (by
  let _atomic_wd_1_1 := (Litex.indexCart _value_i1 _value_i2 _value_i3 h_4 (Litex.isSet _value_i1) h_5 (by
    let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i13 : M.Value), M.mem _raw_i13 (Litex.denote _value_i1) → ((fun (_raw_i13 : M.Value) => True) _raw_i13) → True := (by
        intro _raw_i13 h_46 _
        let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_46)
        have h_46 : Litex.In _value_i13 _value_i1 := h_46
        exact True.intro);
      Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input)))
    exact (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
        intro _raw_i4 h_6 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_6)
        have h_6 : Litex.In _value_i4 _value_i1 := h_6
        exact True.intro);
      Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
        intro _raw_i4 h_6 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_6)
        have h_6 : Litex.In _value_i4 _value_i1 := h_6
        exact True.intro);
      Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
      exact (show Litex.Same _left _right from rfl)) h_7)))
  exact Litex.In _value_i5 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_5 _Host_i3 _rep_i3 _value_i3 h_7 _Host_i5 _rep_i5 _value_i5 h_9 h_1
          have h_54 : Litex.IsNonempty _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have h_55 : Litex.IsNonempty _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          have h_57 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_56 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_56)
              have h_56 : Litex.In _value_i4 _value_i1 := h_56
              exact True.intro);
            Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_59 : Litex.In _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _value_i1) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
              intro _raw_i6 h_58 _
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_58)
              have h_58 : Litex.In _value_i6 _value_i1 := h_58
              exact True.intro);
            Litex.fnSet (let _litex_output := (Litex.familyUnion _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input))) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_86 : Litex.In _value_i5 (Litex.indexCart _value_i1 _value_i2 _value_i3 h_54 (Litex.isSet _value_i1) h_55 (by
            let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i22 : M.Value), M.mem _raw_i22 (Litex.denote _value_i1) → ((fun (_raw_i22 : M.Value) => True) _raw_i22) → True := (by
                intro _raw_i22 h_138 _
                let _value_i22 := Litex.semanticObject (M := M) _raw_i22 (M.member_isSet h_138)
                have h_138 : Litex.In _value_i22 _value_i1 := h_138
                exact True.intro);
              Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i22 : M.Value) => True) _litex_input)))
            exact (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                intro _raw_i4 h_56 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_56)
                have h_56 : Litex.In _value_i4 _value_i1 := h_56
                exact True.intro);
              Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                intro _raw_i4 h_56 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_56)
                have h_56 : Litex.In _value_i4 _value_i1 := h_56
                exact True.intro);
              Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_57))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_88 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i19 : M.Value), M.mem _raw_i19 (Litex.denote _value_i1) → ((fun (_raw_i19 : M.Value) => True) _raw_i19) → True := (by
                          intro _raw_i19 h_89 _
                          let _value_i19 := Litex.semanticObject (M := M) _raw_i19 (M.member_isSet h_89)
                          have h_89 : Litex.In _value_i19 _value_i1 := h_89
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.familyUnion _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i19 : M.Value) => True) _litex_input)))
                      exact Litex.In _value_i5 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i19 : M.Value), M.mem _raw_i19 (Litex.denote _value_i1) → ((fun (_raw_i19 : M.Value) => True) _raw_i19) → True := (by
                                  intro _raw_i19 h_89 _
                                  let _value_i19 := Litex.semanticObject (M := M) _raw_i19 (M.member_isSet h_89)
                                  have h_89 : Litex.In _value_i19 _value_i1 := h_89
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.familyUnion _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i19 : M.Value) => True) _litex_input)))
                              exact (Litex.inOfSame _value_i5 _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _value_i1) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                                  intro _raw_i6 h_58 _
                                  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_58)
                                  have h_58 : Litex.In _value_i6 _value_i1 := h_58
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.familyUnion _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _value_i1) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                                  intro _raw_i6 h_58 _
                                  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_58)
                                  have h_58 : Litex.In _value_i6 _value_i1 := h_58
                                  exact True.intro);
                                Litex.fnSet (let _litex_output := (Litex.familyUnion _value_i2); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)))
                                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                                exact (show Litex.Same _left _right from rfl)) h_59))
                          )
                      )
                    have h_87 : Litex.IsChoiceFunctionFor _value_i1 _value_i2 _value_i3 _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    exact (Litex.indexCartMember (Litex.indexCart _value_i1 _value_i2 _value_i3 h_54 (Litex.isSet _value_i1) h_55 (by
                    let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i21 : M.Value), M.mem _raw_i21 (Litex.denote _value_i1) → ((fun (_raw_i21 : M.Value) => True) _raw_i21) → True := (by
                        intro _raw_i21 h_116 _
                        let _value_i21 := Litex.semanticObject (M := M) _raw_i21 (M.member_isSet h_116)
                        have h_116 : Litex.In _value_i21 _value_i1 := h_116
                        exact True.intro);
                      Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i21 : M.Value) => True) _litex_input)))
                    exact (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_56 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_56)
                        have h_56 : Litex.In _value_i4 _value_i1 := h_56
                        exact True.intro);
                      Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_56 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_56)
                        have h_56 : Litex.In _value_i4 _value_i1 := h_56
                        exact True.intro);
                      Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
                      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) h_57))) _value_i5 h_88 h_87)
                  )
                )
            )
          exact (by
            let _atomic_wd_1_1 := (Litex.indexCart _value_i1 _value_i2 _value_i3 h_54 (Litex.isSet _value_i1) h_55 (by
              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i22 : M.Value), M.mem _raw_i22 (Litex.denote _value_i1) → ((fun (_raw_i22 : M.Value) => True) _raw_i22) → True := (by
                  intro _raw_i22 h_138 _
                  let _value_i22 := Litex.semanticObject (M := M) _raw_i22 (M.member_isSet h_138)
                  have h_138 : Litex.In _value_i22 _value_i1 := h_138
                  exact True.intro);
                Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i22 : M.Value) => True) _litex_input)))
              exact (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_56 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_56)
                  have h_56 : Litex.In _value_i4 _value_i1 := h_56
                  exact True.intro);
                Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                  intro _raw_i4 h_56 _
                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_56)
                  have h_56 : Litex.In _value_i4 _value_i1 := h_56
                  exact True.intro);
                Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                exact (show Litex.Same _left _right from rfl)) h_57)))
            exact h_86)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_indexed_x5f_product_x5f_member_x2f_statement_x2e_lit
