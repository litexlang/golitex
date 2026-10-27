import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_general_x5f_finite_x5f_aggregate_x5f_closure_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.IsFiniteSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_7 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_9 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i2) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_8 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
    have h_8 : Litex.In _value_i4 _value_i2 := h_8
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) (h_1 : Litex.Subset _value_i1 _value_i2), (by
  let _object_w2 := (Litex.finiteAggregateOn false _value_i1 _value_i3 _value_i2 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) h_6 h_1 (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) h_9) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))
  let _object_w4 := (Litex.finiteAggregateOn true _value_i1 _value_i3 _value_i2 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) h_6 h_1 (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) h_9) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))
  exact (((by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w4
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_7 _Host_i3 _rep_i3 _value_i3 h_9 h_1
          let _object_w2 := (Litex.finiteAggregateOn false _value_i1 _value_i3 _value_i2 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) h_6 h_1 (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) h_9) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl))
                )
            )
          let _object_w4 := (Litex.finiteAggregateOn true _value_i1 _value_i3 _value_i2 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) h_6 h_1 (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i2) (Litex.denote _litex_output) (Litex.isSet _value_i2) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) h_9) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))
          have h_3 : (by
            let _atomic_wd_1_0 := _object_w4
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w4
                    exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl))
                )
            )
          exact (And.intro h_2 h_3)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_general_x5f_finite_x5f_aggregate_x5f_closure_x2f_statement_x2e_lit
