import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_left_x5f_multiply_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v6 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_9 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_8 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
    have h_8 : Litex.In _value_i4 (Litex.R (M := M)) := h_8
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_10 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_8 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
    have h_8 : Litex.In _value_i4 (Litex.R (M := M)) := h_8
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_11 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_8 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
    have h_8 : Litex.In _value_i4 (Litex.R (M := M)) := h_8
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_12 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_14 : Litex.In _value_i7 (Litex.R (M := M))) (h_1 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_8 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
      have h_8 : Litex.In _value_i4 (Litex.R (M := M)) := h_8
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_8 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
      have h_8 : Litex.In _value_i4 (Litex.R (M := M)) := h_8
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_8 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
      have h_8 : Litex.In _value_i4 (Litex.R (M := M)) := h_8
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_9)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_17 : Litex.In _value_i5 (Litex.R (M := M)) := h_12
  have h_28 : Litex.In _value_i6 (Litex.R (M := M)) := h_13
  exact Litex.HasFiniteFunctionLimit .left _value_i1 _value_i5 _value_i6)) (h_2 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_8 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
      have h_8 : Litex.In _value_i4 (Litex.R (M := M)) := h_8
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_8 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
      have h_8 : Litex.In _value_i4 (Litex.R (M := M)) := h_8
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_8 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
      have h_8 : Litex.In _value_i4 (Litex.R (M := M)) := h_8
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_10)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_44 : Litex.In _value_i5 (Litex.R (M := M)) := h_12
  have h_55 : Litex.In _value_i7 (Litex.R (M := M)) := h_14
  exact Litex.HasFiniteFunctionLimit .left _value_i2 _value_i5 _value_i7)) (h_4 : ∀ (_value_i8 : Litex.Obj (M := M) M.Value) (h_70 : Litex.In _value_i8 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_11 h_70 True.intro)
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i1 _value_i8 h_9 h_70 True.intro);
  let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i8 h_10 h_70 True.intro);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0)))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), (by
  let _atomic_wd_1_2 := (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_13) (M.real_subset_complex _ h_14))
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i3) := (show Litex.RealFunctionValue M (Litex.denote _value_i3) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_8 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
      have h_8 : Litex.In _value_i4 (Litex.R (M := M)) := h_8
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i3 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_8 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
      have h_8 : Litex.In _value_i4 (Litex.R (M := M)) := h_8
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_8 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8)
      have h_8 : Litex.In _value_i4 (Litex.R (M := M)) := h_8
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_11)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_471 : Litex.In _value_i5 (Litex.R (M := M)) := h_12
  have h_482 : (by
    let _atomic_wd_2_0 := _atomic_wd_1_2
    exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
    let _atomic_wd_2_0 := _atomic_wd_1_2
    exact (Litex.mulInR _value_i6 _value_i7 h_13 h_14))
  exact Litex.HasFiniteFunctionLimit .left _value_i3 _value_i5 _atomic_wd_1_2) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_9 _Host_i2 _rep_i2 _value_i2 h_10 _Host_i3 _rep_i3 _value_i3 h_11 _Host_i5 _rep_i5 _value_i5 h_12 _Host_i6 _rep_i6 _value_i6 h_13 _Host_i7 _rep_i7 _value_i7 h_14 h_1 h_2 h_4
          have h_583 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_582 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
              have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_584 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_582 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
              have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_585 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_582 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
              have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_586 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_587 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          have h_588 : Litex.In _value_i7 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_14
                )
            )
          have h_7 : (by
            let _atomic_wd_1_2 := (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_587) (M.real_subset_complex _ h_588))
            exact Litex.HasFiniteFunctionLimit .left _value_i3 _value_i5 _atomic_wd_1_2) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_984 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_582 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
                          have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_582 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
                                  have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_583)
                          )
                      )
                    have h_985 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_986 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_985
                          )
                      )
                    have h_987 : Litex.In _value_i5 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_586
                          )
                      )
                    have h_990 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_582 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
                          have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_582 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
                                  have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_584)
                          )
                      )
                    have h_991 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_985
                          )
                      )
                    have h_992 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_985
                          )
                      )
                    have h_993 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_996 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_582 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
                          have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i3 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_582 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
                                  have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_585)
                          )
                      )
                    have h_997 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_985
                          )
                      )
                    have h_998 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_985
                          )
                      )
                    have h_999 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_1000 : Litex.HasFiniteFunctionLimit .left _value_i1 _value_i5 _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_1001 : Litex.HasFiniteFunctionLimit .left _value_i2 _value_i5 _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    have h_1003 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_1108 : Litex.In _value_i10 (Litex.R (M := M))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i10 h_996 h_1108 True.intro) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i1 _value_i10 h_984 h_1108 True.intro);
                    let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i10 h_990 h_1108 True.intro);
                    (Litex.mul _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i10 _rep_i10 _value_i10 h_1108
                              exact (h_4 (Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10)) h_1108)
                            )
                          )
                      )
                    have h_1004 : Litex.HasFiniteFunctionLimit .left _value_i3 _value_i5 (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_587) (M.real_subset_complex _ h_588)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              let _atomic_wd_1_2 := (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_587) (M.real_subset_complex _ h_588))
                              have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i3) := (show Litex.RealFunctionValue M (Litex.denote _value_i3) from by
                                let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_582 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
                                  have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                                have _limit_function : Litex.In _value_i3 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_582 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
                                  have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_582 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
                                  have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_996)
                                have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_985
                                have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_985
                                refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                                intro x hx
                                exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              )
                              have h_1735 : Litex.In _value_i5 (Litex.R (M := M)) := h_987
                              have h_1742 : (by
                                let _atomic_wd_2_0 := _atomic_wd_1_2
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
                                let _atomic_wd_2_0 := _atomic_wd_1_2
                                exact (Litex.mulInR _value_i6 _value_i7 h_587 h_588))
                              exact Litex.HasFiniteFunctionLimit .left _value_i3 _value_i5 _atomic_wd_1_2) from (by
                              let _law0_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                intro _raw_i4 h_582 _
                                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
                                have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                              have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_984
                              let _law0_source_domain := (M.standard Litex.StandardSetValue.real)
                              have _law0_domain_set : M.isSet _law0_source_domain := (Litex.isSet (Litex.R (M := M)))
                              have _law0_domain_match : _law0_source_domain = _law0_signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _law0_domain_set _law0_signature.domain_isSet
                                intro x
                                change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
                                rw [Litex.SetSemantics.sep_members]
                                exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                              let _law0_domain := Litex.semanticObject _law0_source_domain _law0_domain_set
                              have _law_real_0 : Litex.RealFunctionValue M (Litex.denote _value_i1) := by
                                refine ⟨_law0_signature, _law0_member, ?_, h_986⟩
                                intro x hx
                                exact h_985 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                              let _law1_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                intro _raw_i4 h_582 _
                                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
                                have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                              have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_990
                              let _law1_source_domain := (M.standard Litex.StandardSetValue.real)
                              have _law1_domain_set : M.isSet _law1_source_domain := (Litex.isSet (Litex.R (M := M)))
                              have _law1_domain_match : _law1_source_domain = _law1_signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _law1_domain_set _law1_signature.domain_isSet
                                intro x
                                change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
                                rw [Litex.SetSemantics.sep_members]
                                exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                              let _law1_domain := Litex.semanticObject _law1_source_domain _law1_domain_set
                              have _law_real_1 : Litex.RealFunctionValue M (Litex.denote _value_i2) := by
                                refine ⟨_law1_signature, _law1_member, ?_, h_992⟩
                                intro x hx
                                exact h_991 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                              let _law2_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                intro _raw_i4 h_582 _
                                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_582)
                                have h_582 : Litex.In _value_i4 (Litex.R (M := M)) := h_582
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                              have _law2_member : Litex.In _value_i3 (Litex.fnSet _law2_signature) := h_996
                              let _law2_source_domain := (M.standard Litex.StandardSetValue.real)
                              have _law2_domain_set : M.isSet _law2_source_domain := (Litex.isSet (Litex.R (M := M)))
                              have _law2_domain_match : _law2_source_domain = _law2_signature.domain := by
                                apply Litex.SetSemantics.ext _ _ _law2_domain_set _law2_signature.domain_isSet
                                intro x
                                change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
                                rw [Litex.SetSemantics.sep_members]
                                exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                              let _law2_domain := Litex.semanticObject _law2_source_domain _law2_domain_set
                              have _law_real_2 : Litex.RealFunctionValue M (Litex.denote _value_i3) := by
                                refine ⟨_law2_signature, _law2_member, ?_, h_998⟩
                                intro x hx
                                exact h_997 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_2 : Litex.denote _law2_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i3) := (_law2_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law2_signature.domain_isSet _law2_member).symm)
                              exact Litex.finiteFunctionLimitMapTwo .left (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i3) (Litex.denote _value_i5) (Litex.denote _value_i6) (Litex.denote _value_i7) (Litex.denote (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_587) (M.real_subset_complex _ h_588))) _law_real_0 _law_real_1 _law_real_2 (_law_domain_1.symm.trans (h_993.trans _law_domain_0)) (_law_domain_2.symm.trans (h_999.trans _law_domain_0)) M.mulValue (fun x y : ℝ => x*y) (by intro x y; rw [M.mul_numbers, Complex.ofReal_mul]) rfl (by
                                intro input hinput
                                have _law_input : M.mem input (Litex.denote _law0_domain) := by
                                  rw [_law_domain_0]
                                  exact hinput
                                exact h_1003 (Litex.semanticObject input (M.member_isSet _law_input)) _law_input
                              ) (continuous_fst.mul continuous_snd) h_1000 h_1001
                            ))
                          )
                      )
                    exact (by
                    let _atomic_wd_1_2 := (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_587) (M.real_subset_complex _ h_588))
                    exact h_1004)
                  )
                )
            )
          exact (by
            let _atomic_wd_1_2 := (Litex.mul _value_i6 _value_i7 (M.real_subset_complex _ h_587) (M.real_subset_complex _ h_588))
            exact h_7)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_left_x5f_multiply_x5f_by_x5f_theorem_x2f_statement_x2e_lit
