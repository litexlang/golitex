import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_pos_x5f_inf_x5f_divide_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v6 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_9 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_12 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_11 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_11)
    have h_11 : Litex.In _value_i4 (Litex.R (M := M)) := h_11
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_13 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_11 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_11)
    have h_11 : Litex.In _value_i4 (Litex.R (M := M)) := h_11
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_14 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_11 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_11)
    have h_11 : Litex.In _value_i4 (Litex.R (M := M)) := h_11
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_15 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_16 : Litex.In _value_i6 (Litex.R (M := M))) (h_1 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_11 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i4 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_11 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i4 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_11 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i4 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_12)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_19 : Litex.In _value_i5 (Litex.R (M := M)) := h_15
  exact Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i5)) (h_2 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_11 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i4 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_11 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i4 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_11 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i4 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_13)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_33 : Litex.In _value_i6 (Litex.R (M := M)) := h_16
  exact Litex.HasInfiniteFunctionLimit .positive _value_i2 _value_i6)) (h_3 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))) (h_5 : ∀ (_value_i7 : Litex.Obj (M := M) M.Value) (h_46 : Litex.In _value_i7 (Litex.R (M := M))), (by
  let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i7 h_13 h_46 True.intro)
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))) (h_7 : ∀ (_value_i8 : Litex.Obj (M := M) M.Value) (h_53 : Litex.In _value_i8 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_14 h_53 True.intro)
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i1 _value_i8 h_12 h_53 True.intro);
  let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i8 h_13 h_53 True.intro);
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (by
      have h_244 : Litex.In _value_i8 (Litex.R (M := M)) :=
        h_53
      exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl _value_i2) (Litex.sameRefl _value_i8)) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (h_5 (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) h_244))
    ))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), (by
  let _atomic_wd_1_1 := (Litex.div _value_i5 _value_i6 (M.real_subset_complex _ h_15) (M.real_subset_complex _ h_16) h_3)
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i3) := (show Litex.RealFunctionValue M (Litex.denote _value_i3) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_11 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i4 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i3 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_11 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i4 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_11 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i4 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_14)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_591 : (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
    let _atomic_wd_2_0 := _atomic_wd_1_1
    exact (Litex.divInR _value_i5 _value_i6 h_15 h_16 (_atomic_wd_2_0).wd.2.2))
  exact Litex.HasInfiniteFunctionLimit .positive _value_i3 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_12 _Host_i2 _rep_i2 _value_i2 h_13 _Host_i3 _rep_i3 _value_i3 h_14 _Host_i5 _rep_i5 _value_i5 h_15 _Host_i6 _rep_i6 _value_i6 h_16 h_1 h_2 h_3 h_5 h_7
          have h_683 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_682 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
              have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_684 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_682 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
              have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          have h_685 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_682 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
              have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_14
                )
            )
          have h_686 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          have h_687 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_16
                )
            )
          have h_10 : (by
            have h_1221 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_3
                  )
              )
            exact (by
              let _atomic_wd_1_1 := (Litex.div _value_i5 _value_i6 (M.real_subset_complex _ h_686) (M.real_subset_complex _ h_687) h_1221)
              exact Litex.HasInfiniteFunctionLimit .positive _value_i3 _atomic_wd_1_1)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_1204 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_682 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
                          have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_682 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
                                  have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_683)
                          )
                      )
                    have h_1205 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_1206 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1205
                          )
                      )
                    have h_1209 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_682 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
                          have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_682 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
                                  have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_684)
                          )
                      )
                    have h_1210 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1205
                          )
                      )
                    have h_1211 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1205
                          )
                      )
                    have h_1212 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_1215 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_682 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
                          have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i3 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_682 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
                                  have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_685)
                          )
                      )
                    have h_1216 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1205
                          )
                      )
                    have h_1217 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1205
                          )
                      )
                    have h_1218 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_1219 : Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_1220 : Litex.HasInfiniteFunctionLimit .positive _value_i2 _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    have h_1221 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3
                          )
                      )
                    have h_1223 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_1314 : Litex.In _value_i10 (Litex.R (M := M))), ¬ Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i10 h_1209 h_1314 True.intro) (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i10 _rep_i10 _value_i10 h_1314
                              exact (h_5 (Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10)) h_1314)
                            )
                          )
                      )
                    have h_1225 : ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_1331 : Litex.In _value_i11 (Litex.R (M := M))), Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_1215 h_1331 True.intro) (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i1 _value_i11 h_1204 h_1331 True.intro);
                    let _wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i11 h_1209 h_1331 True.intro);
                    (Litex.div _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (by
                        have h_1639 : Litex.In _value_i11 (Litex.R (M := M)) :=
                          h_1331
                        exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl _value_i2) (Litex.sameRefl _value_i11)) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (h_1223 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) h_1639))
                      )))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i11 _rep_i11 _value_i11 h_1331
                              exact (h_7 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) h_1331)
                            )
                          )
                      )
                    have h_1226 : Litex.HasInfiniteFunctionLimit .positive _value_i3 (Litex.div _value_i5 _value_i6 (M.real_subset_complex _ h_686) (M.real_subset_complex _ h_687) h_1221) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show (by
                              let _atomic_wd_1_1 := (Litex.div _value_i5 _value_i6 (M.real_subset_complex _ h_686) (M.real_subset_complex _ h_687) h_1221)
                              have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i3) := (show Litex.RealFunctionValue M (Litex.denote _value_i3) from by
                                let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_682 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
                                  have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                                have _limit_function : Litex.In _value_i3 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_682 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
                                  have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_682 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
                                  have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_1215)
                                have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_1205
                                have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_1205
                                refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                                intro x hx
                                exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              )
                              have h_2164 : (by
                                let _atomic_wd_2_0 := _atomic_wd_1_1
                                exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) := (by
                                let _atomic_wd_2_0 := _atomic_wd_1_1
                                exact (Litex.divInR _value_i5 _value_i6 h_686 h_687 (_atomic_wd_2_0).wd.2.2))
                              exact Litex.HasInfiniteFunctionLimit .positive _value_i3 _atomic_wd_1_1) from (by
                              let _law0_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                intro _raw_i4 h_682 _
                                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
                                have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                              have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_1204
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
                                refine ⟨_law0_signature, _law0_member, ?_, h_1206⟩
                                intro x hx
                                exact h_1205 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                              let _law1_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                intro _raw_i4 h_682 _
                                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
                                have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                              have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_1209
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
                                refine ⟨_law1_signature, _law1_member, ?_, h_1211⟩
                                intro x hx
                                exact h_1210 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                              let _law2_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                intro _raw_i4 h_682 _
                                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_682)
                                have h_682 : Litex.In _value_i4 (Litex.R (M := M)) := h_682
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                              have _law2_member : Litex.In _value_i3 (Litex.fnSet _law2_signature) := h_1215
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
                                refine ⟨_law2_signature, _law2_member, ?_, h_1217⟩
                                intro x hx
                                exact h_1216 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_2 : Litex.denote _law2_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i3) := (_law2_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law2_signature.domain_isSet _law2_member).symm)
                              exact Litex.infiniteFunctionLimitDivide .positive (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i3) (Litex.denote _value_i5) (Litex.denote _value_i6) (Litex.denote (Litex.div _value_i5 _value_i6 (M.real_subset_complex _ h_686) (M.real_subset_complex _ h_687) h_1221)) _law_real_0 _law_real_1 _law_real_2 (_law_domain_1.symm.trans (h_1212.trans _law_domain_0)) (_law_domain_2.symm.trans (h_1218.trans _law_domain_0)) rfl h_1221 (by
                                intro input hinput
                                have _law_input : M.mem input (Litex.denote _law0_domain) := by
                                  rw [_law_domain_0]
                                  exact hinput
                                exact h_1223 (Litex.semanticObject input (M.member_isSet _law_input)) _law_input
                              ) (by
                                intro input hinput
                                have _law_input : M.mem input (Litex.denote _law0_domain) := by
                                  rw [_law_domain_0]
                                  exact hinput
                                exact h_1225 (Litex.semanticObject input (M.member_isSet _law_input)) _law_input
                              ) h_1219 h_1220
                            ))
                          )
                      )
                    exact (by
                    let _atomic_wd_1_1 := (Litex.div _value_i5 _value_i6 (M.real_subset_complex _ h_686) (M.real_subset_complex _ h_687) h_1221)
                    exact h_1226)
                  )
                )
            )
          exact (by
            let _atomic_wd_1_1 := (Litex.div _value_i5 _value_i6 (M.real_subset_complex _ h_686) (M.real_subset_complex _ h_687) h_3)
            exact h_10)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_pos_x5f_inf_x5f_divide_x5f_by_x5f_theorem_x2f_statement_x2e_lit
