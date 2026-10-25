import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_aggregate_x5f_closure_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_23 : Litex.IsFiniteSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_25 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_24 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_24)
    have h_24 : Litex.In _value_i3 (Litex.R (M := M)) := h_24
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) (h_1 : Litex.Subset _value_i1 (Litex.R (M := M))), (by
  let _object_w10 := (Litex.finiteAggregate false _value_i1 _value_i2 .real (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)) h_23 h_1 (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.inOfSame _value_i2 _value_i2 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.sameRefl _value_i2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) h_25) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .real _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩))
  let _object_w11 := (Litex.finiteAggregate true _value_i1 _value_i2 .real (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)) h_23 h_1 (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.inOfSame _value_i2 _value_i2 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.sameRefl _value_i2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) h_25) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .real _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩))
  exact (((by
    let _atomic_wd_1_0 := _object_w10
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w11
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_23 _Host_i2 _rep_i2 _value_i2 h_25 h_1
          let _object_w10 := (Litex.finiteAggregate false _value_i1 _value_i2 .real (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)) h_23 h_1 (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.inOfSame _value_i2 _value_i2 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.sameRefl _value_i2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) h_25) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .real _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩))
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w10
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w10
                    exact (Litex.finiteAggregateMember _atomic_wd_1_0 .real rfl))
                )
            )
          let _object_w11 := (Litex.finiteAggregate true _value_i1 _value_i2 .real (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)) h_23 h_1 (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.inOfSame _value_i2 _value_i2 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.sameRefl _value_i2) (Litex.sameRefl (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) h_25) (fun x hx => (Litex.FunctionSignature.oneTarget_domain .real _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩))
          have h_3 : (by
            let _atomic_wd_1_0 := _object_w11
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w11
                    exact (Litex.finiteAggregateMember _atomic_wd_1_0 .real rfl))
                )
            )
          exact (And.intro h_2 h_3)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_aggregate_x5f_closure_x2f_statement_x2e_lit
